#include "base/core.h"

#if OS_LINUX
    #include "os/linux/fs.c"
    #include "os/linux/time.c"
    #include "os/linux/info.c"
    #include "os/linux/threads.c"
#else
    #error "Bad os."
#endif
