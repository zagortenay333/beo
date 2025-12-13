#pragma once

#include "base/mem.h"
#include "base/map.h"
#include "base/string.h"
#include "compiler/lexer.h"

istruct (Interns) {
    Mem *mem;
    Map(String, IString*) map;

    IString *entry_fn_name;
    IString *file_extension;

    #define X(_, K) IString *K;
        EACH_KEYWORD(X)
    #undef X

    #define X(N) IString *builtin_##N;
        EACH_BUILTIN(X)
    #undef X

    #define X(N) IString *attr_##N;
        EACH_ATTRIBUTE(X)
    #undef X
};

Interns *interns_new (Mem *mem, String main_file_path);
IString *intern_str  (Interns *, String);
IString *intern_cstr (Interns *, CString);
