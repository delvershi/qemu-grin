#include <stdio.h>
#include <sys/mman.h>

#include<sys/syscall.h>

#include "qemu.h"
#include "qemu-common.h"
#include "cpu.h"
#include "tcg.h"
#include "trace.h"
#include "disas/disas.h"

#include "ptc.h"
#include "elf.h"

#include "exec/exec-all.h"


#include "qemu/envlist.h"

/* Check coherence of the values of the constants between TCG_* and
   PTC_*. Sadly we have to use this dirty division by zero trick to
   trigger an error from the compiler, in fact, due to using enums and
   not defines, we cannot check the values with a preprocessor
   conditional block. */

  //  exit(1);
#define EQUALS(x, y) (1 / ((int) (x) == (int) (y)))
#define MATCH(pref, x) EQUALS(PTC_ ## x, pref ## x)
#define MATCH2(pref, prefix, a, b) MATCH(pref, prefix ## _ ## a) + MATCH(pref, prefix ## _ ## b)
#define MATCH3(pref, prefix, a, b, c) MATCH(pref, prefix ## _ ## a) + MATCH2(pref, prefix, b, c)
#define MATCH4(pref, prefix, a, b, c, d) MATCH2(pref, prefix, a, b) + MATCH2(pref, prefix, c, d)
#define MATCH5(pref, prefix, a, b, c, d, e) MATCH3(pref, prefix, a, b, e) + MATCH2(pref, prefix, c, d)
#define MATCH7(pref, prefix, a, b, c, d, e, f, g) MATCH4(pref, prefix, a, b, c, d) + MATCH3(pref, prefix, e, f, g)

static int constants_checks __attribute__((unused)) =
  MATCH3(TCG_, TYPE, I32, I64, COUNT) +

  MATCH4(TCG_, COND, NEVER, ALWAYS, EQ, NE) +
  MATCH4(TCG_, COND, LT, GE, LE, GT) +
  MATCH4(TCG_, COND, NEVER, ALWAYS, EQ, NE) +
  MATCH4(TCG_, COND, LTU, GEU, LEU, GTU) +

  MATCH5(, MO, 8, 16, 32, 64, SIZE) +
  MATCH2(, MO, SIGN, BSWAP) + MATCH3(, MO, LE, BE, TE) +
  MATCH7(, MO, UB, UW, UL, SB, SW, SL, Q) +
  MATCH5(, MO, LEUW, LEUL, LESW, LESL, LEQ) +
  MATCH5(, MO, BEUW, BEUL, BESW, BESL, BEQ) +
  MATCH5(, MO, TEUW, TEUL, TESW, TESL, TEQ) +
  MATCH(, MO_SSIZE) +

  MATCH4(, TEMP_VAL, DEAD, REG, MEM, CONST) +

  MATCH3(TCG_, CALL, NO_READ_GLOBALS, NO_WRITE_GLOBALS, NO_SIDE_EFFECTS) +
  MATCH5(TCG_, CALL, NO_RWG, NO_WG, NO_SE, NO_RWG_SE, NO_WG_SE) +
  MATCH(TCG_, CALL_DUMMY_ARG);

#undef EQUALS
#undef MATCH

unsigned long reserved_va = 0;
int singlestep = 0;
unsigned long guest_base = 0;
unsigned long mmap_min_addr = 4096;

//////////////////////////////////////////////////
ArchCPUStateQueueLine CPUQueueLine;
abi_ulong elf_start_data;
abi_ulong elf_end_data;
abi_ulong elf_start_stack;

struct image_info info1, *info = &info1;

int have_guest_base = 0;
unsigned long guest_stack_size = 8*1024*1024UL;
THREAD CPUState *thread_cpu;
const char *exec_path;

void gemu_log(const char *fmt, ...)
{
    va_list ap;

    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
}

///* Wait for pending exclusive operations to complete.  The exclusive lock
//   must be held.  */
//static inline void exclusive_idle(void)
//{   
//    while (pending_cpus) {
//        pthread_cond_wait(&exclusive_resume, &exclusive_lock);
//    }
//}
//
///* Start an exclusive operation.
//   Must only be called from outside cpu_arm_exec.   */
//static inline void start_exclusive(void)
//{
//    CPUState *other_cpu;
//
//    pthread_mutex_lock(&exclusive_lock);
//    exclusive_idle();
//
//    pending_cpus = 1;
//    /* Make all other cpus stop executing.  */
//    CPU_FOREACH(other_cpu) {
//        if (other_cpu->running) {
//            pending_cpus++;
//            cpu_exit(other_cpu);
//        }
//    }
//    if (pending_cpus > 1) {
//        pthread_cond_wait(&exclusive_cond, &exclusive_lock);
//    }
//}
//
///* Finish an exclusive operation.  */
//static inline void __attribute__((unused)) end_exclusive(void)
//{
//    pending_cpus = 0;
//    pthread_cond_broadcast(&exclusive_resume);
//    pthread_mutex_unlock(&exclusive_lock);
//}


void task_settid(TaskState *ts)
{
    if (ts->ts_tid == 0) {
        ts->ts_tid = (pid_t)syscall(SYS_gettid);
    }
}

void stop_all_tasks(void)
{
//    /*
//     * We trust that when using NPTL, start_exclusive()
//     * handles thread stopping correctly.
//     */
//    start_exclusive();
}

/* Assumes contents are already zeroed.  */
void init_task_state(TaskState *ts)
{
    int i;
 
    ts->used = 1;
    ts->first_free = ts->sigqueue_table;
    for (i = 0; i < MAX_SIGQUEUE_SIZE - 1; i++) {
        ts->sigqueue_table[i].next = &ts->sigqueue_table[i + 1];
    }
    ts->sigqueue_table[i].next = NULL;
}

CPUArchState *cpu_copy(CPUArchState *env)
{
    CPUState *cpu = ENV_GET_CPU(env);
#if defined(TARGET_X86_64)
    CPUState *new_cpu = cpu_init("qemu64");
#endif 
    CPUArchState *new_env = new_cpu->env_ptr;
    CPUBreakpoint *bp;
    CPUWatchpoint *wp;

    /* Reset non arch specific state */
    cpu_reset(new_cpu);

    memcpy(new_env, env, sizeof(CPUArchState));

    /* Clone all break/watchpoints.
       Note: Once we support ptrace with hw-debug register access, make sure
       BP_CPU break/watchpoints are handled correctly on clone. */
    QTAILQ_INIT(&new_cpu->breakpoints);
    QTAILQ_INIT(&new_cpu->watchpoints);
    QTAILQ_FOREACH(bp, &cpu->breakpoints, entry) {
        cpu_breakpoint_insert(new_cpu, bp->pc, bp->flags, NULL);
    }
    QTAILQ_FOREACH(wp, &cpu->watchpoints, entry) {
        cpu_watchpoint_insert(new_cpu, wp->vaddr, wp->len, wp->flags, NULL);
    }

    return new_env;
}

///////////////////////////////////////////////////////////

//abi_long do_brk(abi_ulong new_brk) { exit(-1); }

void cpu_list_unlock(void) { /* exit(-1); */ }
void cpu_list_lock(void) { /* exit(-1); */ }

#ifdef TARGET_I386
uint64_t cpu_get_tsc(CPUX86State *env) {
    return 0;
}

int cpu_get_pic_interrupt(CPUX86State *env)
{
    return -1;
}

#endif

static PTCInstructionList dump_tinycode(TCGContext *s);

PTCOpcodeDef *ptc_opcode_defs;
PTCHelperDef *ptc_helper_defs;
unsigned ptc_helper_defs_size;

int32_t *ptc_exception_syscall;
uint32_t is_indirect = 0;
uint32_t is_call = 0;
target_ulong callnext = 0;

static unsigned long cs_base = 0;
static CPUState *cpu = NULL;

#if defined(TARGET_X86_64) || defined(TARGET_I386)
# define CPU_STRUCT X86CPU
#elif defined(TARGET_ARM)
# define CPU_STRUCT ARMCPU
#elif defined(TARGET_MIPS)
# define CPU_STRUCT MIPSCPU
#elif defined(TARGET_S390X)
# define CPU_STRUCT S390CPU
#endif

typedef struct {
  target_ulong start;
  target_ulong end;
} AddressRange;

#define MAX_RANGES 10
static AddressRange ranges[MAX_RANGES];

static CPU_STRUCT initialized_state;

int ptc_load(void *handle, PTCInterface *output, const char *ptc_filename) {

  PTCInterface result = { 0 };

  ptc_init(ptc_filename);

#if defined(TARGET_X86_64) || defined(TARGET_I386)
  result.pc = offsetof(CPUX86State, eip);
  result.sp = offsetof(CPUX86State, regs[R_ESP]);
  CPUX86State *env = (CPUX86State *)cpu->env_ptr;
  result.regs = env->regs;
#elif defined(TARGET_ARM)
  result.pc = offsetof(CPUARMState, regs[15]);
  result.sp = offsetof(CPUARMState, regs[13]);
#elif defined(TARGET_MIPS)
  result.pc = offsetof(CPUMIPSState, active_tc.PC);
  result.sp = offsetof(CPUMIPSState, active_tc.gpr[29]);
#elif defined(TARGET_S390X)
  result.pc = offsetof(CPUS390XState, psw.addr);
  result.sp = offsetof(CPUS390XState, regs[15]);
#endif

  result.exception_index =
    (offsetof(CPU_STRUCT, parent_obj) + offsetof(CPUState, exception_index))
    - offsetof(CPU_STRUCT, env);

  result.get_condition_name = &ptc_get_condition_name;
  result.get_load_store_name = &ptc_get_load_store_name;
  result.parse_load_store_arg = &ptc_parse_load_store_arg;
  result.get_arg_label_id = &ptc_get_arg_label_id;
  result.mmap = &ptc_mmap;
  result.translate = &ptc_translate;
  result.disassemble = &ptc_disassemble;
  result.do_syscall2 = &ptc_do_syscall2;
  result.storeCPUState = &ptc_storeCPUState;
  result.getBranchCPUeip = &ptc_getBranchCPUeip;
  result.deletCPULINEState = &ptc_deletCPULINEState;
  result.is_image_addr = &ptc_is_image_addr;
  result.isValidExecuteAddr = &ptc_isValidExecuteAddr;

  result.opcode_defs = ptc_opcode_defs;
  result.helper_defs = ptc_helper_defs;
  result.helper_defs_size = ptc_helper_defs_size;
  result.initialized_env = (uint8_t *) &initialized_state.env;
  
  result.exception_syscall = ptc_exception_syscall;
  result.isIndirect = &is_indirect;
  result.isCall = &is_call;
  result.CallNext = &callnext;

  *output = result;

  return 0;
}

static void add_helper(gpointer key, gpointer value, gpointer user_data) {
  TCGHelperInfo *helper = value;
  unsigned *count = user_data;
  unsigned index = --(*count);

  ptc_helper_defs[index].func = helper->func;
  ptc_helper_defs[index].name = helper->name;
  ptc_helper_defs[index].flags = helper->flags;
}

static void sig_handle(int signum){
  printf("do segment fault %d\n",signum);
  siglongjmp(cpu->jmp_env,1);
}

void ptc_init(const char *filename) {
  int i = 0;

//////
   char **target_environ, **wrk;
   char **target_argv;
   int target_argc;
   //struct image_info info1, *info = &info1;
   struct linux_binprm bprm;
   TaskState *ts;
   int ret,execfd;
   envlist_t *envlist;
   struct target_pt_regs regs1, *regs = &regs1;
   
   memset(regs,0,sizeof(struct target_pt_regs));
   /* Zero out image_info */
   memset(info, 0, sizeof(struct image_info));
   memset(&bprm, 0, sizeof (bprm));
//   CPUState *cpu = CPU(x86_env_get_cpu(env));
   exec_path = filename;
//////


  if (cpu == NULL) {
    /* init guest base */
   // guest_base = 0xb0000000;
    guest_base = 0;

    /* init TCGContext */
    tcg_exec_init(0);

    /* init QOM */
    module_call_init(MODULE_INIT_QOM);

    /* init env and cpu */
#if defined(TARGET_I386)

#if defined(TARGET_X86_64)
    cpu = cpu_init("qemu64");
#else
    cpu = cpu_init("qemu32");
#endif

#elif defined(TARGET_MIPS)
#if defined(TARGET_ABI_MIPSN32) || defined(TARGET_ABI_MIPSN64)
    cpu = cpu_init("5KEf");
#else
    cpu = cpu_init("24Kf");
#endif
#else
    cpu = cpu_init("any");
#endif

    assert(cpu != NULL);

    /* Reset CPU */
    cpu_reset(cpu);

////////////////////////////////

    thread_cpu = cpu;

    if ((envlist = envlist_create()) == NULL) {
        (void) fprintf(stderr, "Unable to allocate envlist\n");
        exit(1);
    }
    /* add current environment into the list */
    for (wrk = environ; *wrk != NULL; wrk++) {
        (void) envlist_setenv(envlist, *wrk);
    }

    target_environ = envlist_to_environ(envlist, NULL);
    envlist_free(envlist);

    /*
     * Prepare copy of argv vector for target.
     */
    target_argc = 1;//argc-optind, dynamic execute don't need argemuent
    target_argv = calloc(target_argc + 1, sizeof (char *));
    if (target_argv == NULL) {
	(void) fprintf(stderr, "Unable to allocate memory for target_argv\n");
	exit(1);
    }
    /*
     * If argv0 is specified (using '-0' switch) we replace
     * argv[0] pointer with the given one.
     */
    /**** 
    i = 0;

    if (argv0 != NULL) {
        target_argv[i++] = strdup(argv0);
    }
    ****/
    target_argv[target_argc-1] =strdup(filename);
    target_argv[target_argc] = NULL;

    ts = g_malloc0 (sizeof(TaskState));
    init_task_state(ts);
    /* build Task State */
    ts->info = info;
    ts->bprm = &bprm;
    cpu->opaque = ts;
    task_settid(ts);

    execfd = qemu_getauxval(AT_EXECFD);
    if (execfd == 0) {
        execfd = open(filename, O_RDONLY);
        if (execfd < 0) {
            printf("Error while loading %s: %s\n", filename, strerror(errno));
            _exit(1);
        }
    }

    ret = loader_exec(execfd, filename, target_argv, target_environ, regs,
        info, &bprm);
    if (ret != 0) {
        printf("Error while loading %s: %s\n", filename, strerror(-ret));
        _exit(1);
    }
    for (wrk = target_environ; *wrk; wrk++) {
        free(*wrk);
    }

    free(target_environ);

    target_set_brk(info->brk);
    syscall_init();
    signal_init();

   /* Get ELF data segment */
   elf_start_data = info->start_data;
   elf_end_data = info->end_data;
   /* Get Stack segment */
   elf_start_stack = info->start_stack; 

   /* Set signal to do with SIGSEGV */
   if(signal(SIGSEGV,sig_handle)==SIG_ERR)
     fprintf(stderr,"signal(SIGSEGV) error\n");
 
////////////////////////////////

    tcg_prologue_init(&tcg_ctx);

    initialize_cpu_state(cpu->env_ptr,regs);

    /* set logging for tiny code dumping */
    qemu_set_log(CPU_LOG_TB_OP | CPU_LOG_TB_OP_OPT);

    initialized_state = *(container_of(cpu->env_ptr, CPU_STRUCT, env)); 
   
    ptc_exception_syscall = &(cpu->exception_index);

  }
  
  if (ptc_opcode_defs == NULL) {
    ptc_opcode_defs = (PTCOpcodeDef *) calloc(sizeof(PTCOpcodeDef), tcg_op_defs_max);

    for (i = 0; i < tcg_op_defs_max; i++) {
      ptc_opcode_defs[i].name = tcg_op_defs[i].name;
      ptc_opcode_defs[i].nb_oargs = tcg_op_defs[i].nb_oargs;
      ptc_opcode_defs[i].nb_iargs = tcg_op_defs[i].nb_iargs;
      ptc_opcode_defs[i].nb_cargs = tcg_op_defs[i].nb_cargs;
      ptc_opcode_defs[i].nb_args = tcg_op_defs[i].nb_args;
    }
  }

  if (ptc_helper_defs == NULL) {
    TCGContext *s = &tcg_ctx;
    GHashTable *helper_table = s->helpers;
    unsigned helper_table_size = g_hash_table_size(helper_table);

    ptc_helper_defs_size = helper_table_size;
    ptc_helper_defs = (PTCHelperDef *) calloc(sizeof(PTCHelperDef), helper_table_size);

    g_hash_table_foreach(helper_table, add_helper, &helper_table_size);
  }
  initArchCPUStateQueueLine();
}

static TranslationBlock *tb_alloc2(target_ulong pc)
{
    TranslationBlock *tb;

    if (tcg_ctx.tb_ctx.nb_tbs >= tcg_ctx.code_gen_max_blocks ||
        (tcg_ctx.code_gen_ptr - tcg_ctx.code_gen_buffer) >=
         tcg_ctx.code_gen_buffer_max_size) {
        return NULL;
    }
    tb = &tcg_ctx.tb_ctx.tbs[tcg_ctx.tb_ctx.nb_tbs++];
    tb->pc = pc;
    tb->cflags = 0;
    return tb;
}

static PTCTemp copy_temp(TCGTemp original) {
  PTCTemp result = { 0 };

  result.reg = original.reg;
  result.mem_reg = original.mem_reg;
  result.val_type = original.val_type;
  result.base_type = original.base_type;
  result.type = original.type;
  result.fixed_reg = original.fixed_reg;
  result.mem_coherent = original.mem_coherent;
  result.mem_allocated = original.mem_allocated;
  result.temp_local = original.temp_local;
  result.temp_allocated = original.temp_allocated;
  result.val = original.val;
  result.mem_offset = original.mem_offset;
  result.name = original.name;

  return result;
}

static PTCInstructionList dump_tinycode(TCGContext *s) {
    TCGOp *op = NULL;
    int oi = 0;
    int j = 0;

    PTCInstructionList result = { 0 };

    unsigned arguments_count = 0;

    PTCInstruction *current_instruction = NULL;
    TCGOpcode c;
    const TCGOpDef *def = NULL;
    const TCGArg *args = NULL;

    for (oi = s->gen_first_op_idx; oi >= 0; oi = op->next) {
      result.instruction_count++;

     // printf("oi: %d\n",oi);

      op = &s->gen_op_buf[oi];
      c = op->opc;
      def = &tcg_op_defs[c];

      if (c == INDEX_op_debug_insn_start) {
        arguments_count += 2;
      } else if (c == INDEX_op_call) {
        arguments_count += op->callo + op->calli + def->nb_cargs;
      } else {
        arguments_count += def->nb_oargs + def->nb_iargs + def->nb_cargs;
      }
    }

    result.instructions = (PTCInstruction *) calloc(sizeof(PTCInstruction), result.instruction_count);
    result.arguments = (PTCInstructionArg *) calloc(sizeof(PTCInstructionArg), arguments_count);

    /* Copy the temp values */
    result.total_temps = s->nb_temps;
    result.global_temps = s->nb_globals;

  //  printf("nb_temps: %d  nb_globals: %d\n",s->nb_temps,s->nb_globals);

    result.temps = (PTCTemp *) calloc(sizeof(PTCTemp), result.total_temps);

    for (oi = 0; oi < s->nb_temps; oi++)
      result.temps[oi] = copy_temp(s->temps[oi]);

    /* Go through all the instructions again and collect the information */

    result.instruction_count = 0;
    arguments_count = 0;
    for (oi = s->gen_first_op_idx; oi >= 0; oi = op->next) {
      unsigned int total_new = 0;

      current_instruction = &result.instructions[result.instruction_count];
      result.instruction_count++;

      op = &s->gen_op_buf[oi];
      args = &s->gen_opparam_buf[op->args];

      current_instruction->opc = (PTCOpcode) s->gen_op_buf[oi].opc;
      current_instruction->callo = s->gen_op_buf[oi].callo;
      current_instruction->calli = s->gen_op_buf[oi].calli;

      c = current_instruction->opc;
      def = &tcg_op_defs[c];

      current_instruction->args = &result.arguments[arguments_count];

      if (c == INDEX_op_debug_insn_start)
        total_new = 2;
      else if (c == INDEX_op_call)
        total_new = current_instruction->callo + current_instruction->calli + def->nb_cargs;
      else
        total_new = def->nb_oargs + def->nb_iargs + def->nb_cargs;

      for (j = 0; j < total_new; j++)
        result.arguments[arguments_count + j] = args[j];

      arguments_count += total_new;
    }

   // *instructions = result;
    return result;
}

extern void tb_link_page(TranslationBlock *tb, tb_page_addr_t phys_pc,
                         tb_page_addr_t phys_page2);

static TranslationBlock *tb_gen_code2(TCGContext *s, CPUState *cpu,
                                     target_ulong pc, target_ulong cs_base,
                                     int flags, int cflags,
                                     PTCInstructionList *instructions)
{
    CPUArchState *env = cpu->env_ptr;
    TranslationBlock *tb;
    tb_page_addr_t phys_pc,phys_page2;
    target_ulong virt_page2;
    int i = 0;

    tcg_insn_unit *gen_code_buf;
    int gen_code_size;

    PTCInstructionList instructions1;

    phys_pc = get_page_addr_code(env, pc);

    if (use_icount) {
        cflags |= CF_USE_ICOUNT;
    }

    tb = tb_alloc2(pc);
    if (!tb) {
        /* flush must be done */
        tb_flush(cpu);
        /* cannot fail at this point */
        tb = tb_alloc2(pc);
        /* Don't forget to invalidate previous TB info.  */
        tcg_ctx.tb_ctx.tb_invalidated_flag = 1;
    }

    tb->tc_ptr = tcg_ctx.code_gen_ptr;
    tb->cs_base = cs_base;
    tb->flags = flags;
    tb->cflags = cflags;
    tb->isIndirect = 0;
    tb->isCall = 0;
    tb->CallNext = 0;

    for (i = 0; i < MAX_RANGES; i++)
      if (ranges[i].start <= pc && pc < ranges[i].end)
        break;
    assert(i != MAX_RANGES);
    tb->max_pc = ranges[i].end;

    // From cpu_gen_code
    tcg_func_start(s);

    gen_intermediate_code(env, tb);

   // tcg_dump_ops(s);
    instructions1 = dump_tinycode(s);
    *instructions = instructions1;

    /* generate machine code */
    gen_code_buf = tb->tc_ptr;
    tb->tb_next_offset[0] = 0xffff;
    tb->tb_next_offset[1] = 0xffff;
    s->tb_next_offset = tb->tb_next_offset;

#ifdef USE_DIRECT_JUMP
    s->tb_jmp_offset = tb->tb_jmp_offset;
    s->tb_next = NULL;
#else
    s->tb_jmp_offset = NULL;
    s->tb_next = tb->tb_next;
#endif

//#ifdef CONFIG_PROFILER
//    s->tb_count++;
//    s->interm_time += profile_getclock() - ti;
//    s->code_time -= profile_getclock();
//#endif
    gen_code_size = tcg_gen_code(s, gen_code_buf);
//#ifdef CONFIG_PROFILER
//    s->code_time += profile_getclock();
//    s->code_in_len += tb->size;
//    s->code_out_len += gen_code_size;
//#endif
//
#ifdef DEBUG_DISAS
    if (qemu_loglevel_mask(CPU_LOG_TB_OUT_ASM)) 
  {
      qemu_log("OUT: [size=%d]\n", gen_code_size);
      log_disas(tb->tc_ptr, gen_code_size);
      qemu_log("\n");
      qemu_log_flush();
  }
#endif
    tcg_ctx.code_gen_ptr = (void *)(((uintptr_t)tcg_ctx.code_gen_ptr + 
            gen_code_size + CODE_GEN_ALIGN - 1) & ~(CODE_GEN_ALIGN - 1));
    /* end generate */

    /* check next page if needed */
    virt_page2 = (pc + tb->size - 1) & TARGET_PAGE_MASK;
    phys_page2 = -1;
    if ((pc & TARGET_PAGE_MASK) != virt_page2) 
    {
        phys_page2 = get_page_addr_code(env, virt_page2);
    } 
    tb_link_page(tb, phys_pc, phys_page2);

    return tb;
}

void ptc_mmap(uint64_t virtual_address, const void *code, size_t code_size) {
  abi_long mmapd_address;
  unsigned i;

  mmapd_address = target_mmap((abi_ulong) virtual_address,
                              (abi_ulong) code_size,
                              PROT_READ | PROT_WRITE | PROT_EXEC,
                              MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED,
                              -1,
                              0);
  memcpy((void *) g2h(virtual_address), code, code_size);

  assert(mmapd_address == (abi_ulong) virtual_address);

  for (i = 0; i < MAX_RANGES; i++) {
    if (ranges[i].start == ranges[i].end
        && ranges[i].end == 0) {
      ranges[i].start = virtual_address;
      ranges[i].end = virtual_address + code_size;
      return;
    }
  }

  assert(false);
}

/* Execute a TB, and fix up the CPU state afterwards if necessary */
static inline tcg_target_ulong cpu_tb_exec(CPUState *cpu, uint8_t *tb_ptr)
{
    CPUArchState *env = cpu->env_ptr;
    uintptr_t next_tb;

//#if defined(DEBUG_DISAS)
//    if (qemu_loglevel_mask(CPU_LOG_TB_CPU)) 
//    {
//#if defined(TARGET_I386)
//        log_cpu_state(cpu, CPU_DUMP_CCOP);
//#elif defined(TARGET_M68K)
//        /* ??? Should not modify env state for dumping.  */
//        cpu_m68k_flush_flags(env, env->cc_op);
//        env->cc_op = CC_OP_FLAGS;
//        env->sr = (env->sr & 0xffe0) | env->cc_dest | (env->cc_x << 4);
//        log_cpu_state(cpu, 0);
//#else
//        log_cpu_state(cpu, 0);
//#endif
//    }
//#endif /* DEBUG_DISAS */
    cpu->can_do_io = 0;

    next_tb = tcg_qemu_tb_exec(env, tb_ptr);

    cpu->can_do_io = 1;

//    trace_exec_tb_exit((void *) (next_tb & ~TB_EXIT_MASK),
//                       next_tb & TB_EXIT_MASK);

//    if ((next_tb & TB_EXIT_MASK) > TB_EXIT_IDX1) {
//        /* We didn't start executing this TB (eg because the instruction
//         * counter hit zero); we must restore the guest PC to the address
//         * of the start of the TB.
//         */
//        CPUClass *cc = CPU_GET_CLASS(cpu);
//        TranslationBlock *tb = (TranslationBlock *)(next_tb & ~TB_EXIT_MASK);
//        if (cc->synchronize_from_tb) {
//            cc->synchronize_from_tb(cpu, tb);
//        } else {
//            assert(cc->set_pc);
//            cc->set_pc(cpu, tb->pc);
//        }
//    }
//
//    if ((next_tb & TB_EXIT_MASK) == TB_EXIT_REQUESTED) {
//        /* We were asked to stop executing TBs (probably a pending
//         * interrupt. We've now stopped, so clear the flag.
//         */
//        cpu->tcg_exit_req = 0;
//    }

    return next_tb;

}

/* TODO: error management */
size_t ptc_translate(uint64_t virtual_address, PTCInstructionList *instructions, uint64_t *dymvirtual_address) {
//unsigned long ptc_translate(uint64_t virtual_address, PTCInstructionList *instructions, uint64_t * dymvirtual_address) {
    TCGContext *s = &tcg_ctx;
    TranslationBlock *tb = NULL;

    uint8_t *tc_ptr;
    CPUArchState *env = (CPUArchState *)cpu->env_ptr;

    is_indirect = 0;
    is_call = 0;
    env->eip = virtual_address;

    target_ulong temp;
    int flags = 0;
    cpu_get_tb_cpu_state(cpu->env_ptr, &temp, &temp, &flags);

#if defined(TARGET_S390X)
    flags |= FLAG_MASK_32 | FLAG_MASK_64;
#endif

    tb = tb_gen_code2(s, cpu, (target_ulong) virtual_address, cs_base, flags, 0,instructions);

    if(tb->isIndirect)
      is_indirect = 1;
    if(tb->isCall){
      is_call = 1;
      callnext = tb->CallNext;
    }
    
   // printf("virtual_address: %lx  tb ->pc: %lx\n",virtual_address,tb->pc);
  
    if(sigsetjmp(cpu->jmp_env,1)==0){
    
      tc_ptr = tb->tc_ptr;
      cpu_tb_exec(cpu, tc_ptr);
    }
    else{
    
      printf("explore branch:  %lx\n",virtual_address);
      cpu->exception_index = 11;
   // exit(1);
   // printf("exception_next_eip: %lx\n",env->exception_next_eip);
    }

    *dymvirtual_address = env->eip;
    return (size_t) tb->size;
   // return env->eip;
}

void ptc_deletCPULINEState(void){
  CPUArchState *env = (CPUArchState *)cpu->env_ptr;
  BranchState datatmp;
  datatmp = deletArchCPUStateQueueLine();
  *env = datatmp.cpu_data;
  fprintf(stderr,"load......... CPU %lx\n",env->eip);
  fprintf(stderr,"load......... rax %lx\n",env->regs[0]);
  fprintf(stderr,"load......... rsp %lx\n",env->regs[4]);
  
  /* Load ELF data segments */
  memcpy((void *)elf_start_data,datatmp.elf_data,elf_end_data - elf_start_data);
  free(datatmp.elf_data);
  /* Load ELF stack segments */
  memcpy((void *)env->regs[4],datatmp.elf_stack,elf_start_stack-(abi_ulong)env->regs[4]);
  free(datatmp.elf_stack);
}

void ptc_storeCPUState(void) {
  CPUArchState *env = (CPUArchState *)cpu->env_ptr;
  CPUArchState *new_env;
  
  new_env = cpu_copy(env);
  fprintf(stderr,"store CPU %lx\n",new_env->eip);
  fprintf(stderr,"store rax %lx\n",new_env->regs[0]);
  
  /* Store ELF data segments */
  void *pdata = (void *)malloc(elf_end_data - elf_start_data);
  if(pdata == NULL){
    fprintf(stderr,"Alloc data memory failed!\n");
    exit(0);
  }
  memcpy(pdata,(void *)elf_start_data,elf_end_data - elf_start_data);
 
  /* Store ELF stack segments */
  void *pstack = (void *)malloc(elf_start_stack - (abi_ulong)env->regs[4]);
  if(pstack == NULL){
    fprintf(stderr,"Alloc stack memory failed!\n");
    exit(0);
  }
  memcpy(pstack,(void *)env->regs[4],elf_start_stack - (abi_ulong)env->regs[4]);

  insertArchCPUStateQueueLine(*new_env,pdata,pstack); 
}

void ptc_getBranchCPUeip(void){ 
  traversArchCPUStateQueueLine();
}

uint32_t ptc_is_image_addr(uint64_t va){
  //printf("brk:%lx\n mmap:%lx\n ",info->brk,info->mmap);
  if(va>=info->start_code && va<=info->end_code)
    return 1;

  if(va>=info->start_data && va<=info->end_data)
    return 1;

  if(va>=info->brk && va<=info->start_mmap){
    fprintf(stderr,"Unknow address: %lx brk: %lx mmap: %lx\n",va,info->brk,info->mmap);
    exit(0);
    return 1;
  }
 
  if(va<=info->start_stack && va>=0x4000000000)
    return 1;

  fprintf(stderr,"Unknow address access: %lx\n",va);
  return 0;
}

uint32_t ptc_isValidExecuteAddr(uint64_t va){
  if(va>=info->start_code && va<=info->end_code)
    return 1;

  return 0;
}

unsigned long ptc_do_syscall2(void){
    CPUArchState *env = (CPUArchState *)cpu->env_ptr;

    if(env->regs[R_EAX]==231){
      env->eip = env->exception_next_eip;
      cpu->exception_index = -1;
      
      return 0;
    }
    if(env->regs[R_EAX]==202){
      env->eip = env->exception_next_eip;
      cpu->exception_index = -1;
   
      return 0;//TARGET_NR_futex
    }
    
    env->regs[R_EAX] = do_syscall(env,
				  env->regs[R_EAX],
				  env->regs[R_EDI],
				  env->regs[R_ESI],
				  env->regs[R_EDX],
				  env->regs[10],
				  env->regs[8],
				  env->regs[9],
				  0,0);
    env->eip = env->exception_next_eip;
    cpu->exception_index = -1; 

    // Deal with CPUX86State->df, I don't know why do this?   
    CC_SRC = env->eflags & (CC_O | CC_S | CC_Z | CC_A | CC_P | CC_C); 
    env->df = 1 - (2 * ((env->eflags >> 10) & 1));
    CC_OP = CC_OP_EFLAGS;
    env->eflags &= ~(DF_MASK | CC_O | CC_S | CC_Z | CC_A | CC_P | CC_C);   
 
    return env->eip; 
}

const char *ptc_get_condition_name(PTCCondition condition) {
  switch (condition) {
  case PTC_COND_NEVER: return "never";
  case PTC_COND_ALWAYS: return "always";
  case PTC_COND_EQ: return "eq";
  case PTC_COND_NE: return "ne";
  case PTC_COND_LT: return "lt";
  case PTC_COND_GE: return "ge";
  case PTC_COND_LE: return "le";
  case PTC_COND_GT: return "gt";
  case PTC_COND_LTU: return "ltu";
  case PTC_COND_GEU: return "geu";
  case PTC_COND_LEU: return "leu";
  case PTC_COND_GTU: return "gtu";
  default: return NULL;
  }
}

const char *ptc_get_load_store_name(PTCLoadStoreType type) {
  switch (type) {
  case PTC_MO_UB: return "ub";
  case PTC_MO_SB: return "sb";
  case PTC_MO_LEUW: return "leuw";
  case PTC_MO_LESW: return "lesw";
  case PTC_MO_LEUL: return "leul";
  case PTC_MO_LESL: return "lesl";
  case PTC_MO_LEQ: return "leq";
  case PTC_MO_BEUW: return "beuw";
  case PTC_MO_BESW: return "besw";
  case PTC_MO_BEUL: return "beul";
  case PTC_MO_BESL: return "besl";
  case PTC_MO_BEQ: return "beq";
  default: return NULL;
  }
}

PTCLoadStoreArg ptc_parse_load_store_arg(PTCInstructionArg arg) {
  PTCLoadStoreArg result = { 0 };

  result.raw_op = get_memop((TCGMemOpIdx) arg);
  if (result.raw_op & ~(MO_AMASK | MO_BSWAP | MO_SSIZE)) {
    result.access_type = PTC_MEMORY_ACCESS_UNKNOWN;
  } else {
    if (result.raw_op & MO_AMASK) {
      if ((result.raw_op & MO_AMASK) == MO_ALIGN) {
        result.access_type = PTC_MEMORY_ACCESS_ALIGNED;
      } else {
        result.access_type = PTC_MEMORY_ACCESS_UNALIGNED;
      }
    } else {
      result.access_type = PTC_MEMORY_ACCESS_NORMAL;
    }
  }

  result.type = result.raw_op & (MO_BSWAP | MO_SSIZE);
  result.mmu_index = get_mmuidx((TCGMemOpIdx) arg);
  return result;
}

unsigned ptc_get_arg_label_id(PTCInstructionArg arg) {
  TCGLabel *label = arg_label((TCGArg) arg);
  return label->id;
}

void ptc_disassemble(FILE *output, uint32_t buffer, size_t buffer_size,
                     int max) {
  int flags = 0;
#ifdef TARGET_X86_64
  /* Force 64-bit decoding */
  flags = 2;
#endif
  target_disas_max(output, cpu, /* GUEST_BASE + */ buffer, buffer_size, flags, max);
}

void initArchCPUStateQueueLine(void){
  CPUQueueLine.front = CPUQueueLine.rear = (QueuePtr)malloc(sizeof(QNode));
  if(CPUQueueLine.front == NULL){
    fprintf(stderr,"Initial queue node failed!\n");
    exit(0);
  }  
  CPUQueueLine.front->next = NULL;
}

void insertArchCPUStateQueueLine(CPUArchState element,void *elf_data,void *elf_stack){
  QueuePtr q = (QueuePtr)malloc(sizeof(QNode));
  if(q == NULL){
    fprintf(stderr,"Alloca queue node failed!\n");
  }
  q->data.cpu_data = element;
  q->data.elf_data = elf_data;
  q->data.elf_stack = elf_stack;
  q->next = NULL;
  // CPUQueueLine.rear represents the last element 
  CPUQueueLine.rear->next = q;
  CPUQueueLine.rear = q;
}

int isEmpty(void){ return CPUQueueLine.front == CPUQueueLine.rear?1:0; }

BranchState deletArchCPUStateQueueLine(void){
  BranchState element;
  QueuePtr q = CPUQueueLine.front->next;
  if(!isEmpty()){
     element.cpu_data = q->data.cpu_data;
     element.elf_data = q->data.elf_data;
     element.elf_stack = q->data.elf_stack;
     CPUQueueLine.front->next  = q->next;
     if(CPUQueueLine.rear == q){
       CPUQueueLine.rear = CPUQueueLine.front;
     }
    free(q); 
  }
  else{
    fprintf(stderr,"Branch CPU state line is null!\n");
    exit(0);
  }
  
  return element;
}

void traversArchCPUStateQueueLine(void) {
  QueuePtr p = CPUQueueLine.front->next;
  while(p!=NULL){
    fprintf(stderr,"CPU State eip: %lx\n",p->data.cpu_data.eip);
    p = p->next;
  }
}


