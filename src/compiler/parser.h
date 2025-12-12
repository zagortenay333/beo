#pragma once

#include "base/core.h"

istruct (Parser);

Parser       *par_new        (Mem *, Interns *);
AstFile      *par_parse_file (Parser *, IString *);
ArrayAstNote *par_get_notes  (Parser *, AstId);
