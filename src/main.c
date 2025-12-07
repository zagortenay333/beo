#include "base/core.h"
#include "base/mem.h"
#include "base/array.h"
#include "base/log.h"
#include "os/fs.h"
#include "compiler/interns.h"
#include "compiler/vm.h"

istruct (CmdLine) {
    U64 cursor;
    Slice(CString) args;
    String main_file_path;
};

static Void cli_print_options () {
    printf(
        "-h        Print command line options.\n"
        "-i <path> File path of main file.\n"
    );
}

static String cli_eat (CmdLine *cli, CString error_msg) {
    String s;

    if (cli->cursor < cli->args.count) {
        s = str(array_get(&cli->args, cli->cursor));
        cli->cursor++;
    } else {
        s = (String){};
        log_msg_fmt(LOG_ERROR, "", 1, "%s", error_msg);
    }

    return s;
}

static CmdLine cli_parse (Int argc, CString *argv) {
    CmdLine cli = { .cursor=1, .args={ .data=argv, .count=cast(U64, argc) } };
    log_scope(ls, 1);

    while (cli.cursor < cli.args.count) {
        String arg = cli_eat(&cli, "");

        if (str_match(arg, str("-h"))) {
            cli_print_options();
        } else if (str_match(arg, str("-i"))) {
            cli.main_file_path = cli_eat(&cli, "Command line argument '-i' missing file operand.");
        } else {
            log_msg_fmt(LOG_ERROR, "", 1, "Unknown command line argument '%.*s'.", STR(arg));
        }

        if (ls->count[LOG_ERROR]) break;
    }

    if (cli.args.count == 1) cli_print_options();
    return cli;
}

static Int print1 (Vm *vm, SliceVmReg args) {
    array_iter_from (arg, &args, 2, *) printf("====== %li\n", arg->i64);
    VmReg *result = array_ref(&args, 0);
    result->tag = VM_REG_INT;
    result->i64 = args.count - 2;
    return 0;
}

static Int print2 (Vm *vm, SliceVmReg args) {
    array_iter_from (arg, &args, 2, *) printf("-------- %li\n", arg->i64);
    VmReg *result = array_ref(&args, 0);
    result->tag = VM_REG_INT;
    result->i64 = args.count - 2;
    return 0;
}

Int main (Int argc, CString *argv) {
    random_setup();
    tmem_setup(mem_root, 1*MB);
    log_setup(mem_root, 4*KB);
    log_scope(ls, 1);

    CmdLine cli = cli_parse(argc, argv);

    Mem *mem = cast(Mem*, arena_new(mem_root, 1*MB));

    Vm *vm = vm_new(mem);

    vm_ffi_new(vm, str("foo"));
    vm_ffi_add(vm, str("foo"), str("print1"), print1);

    vm_ffi_new(vm, str("bar"));
    vm_ffi_add(vm, str("bar"), str("print2"), print2);

    vm_set_prog(vm, cli.main_file_path);
    vm_print(vm);
    vm_run(vm);
}
