/* Lean 4.35.0 runtime compatibility for PID-virtualized execution hosts.
 * Only map the caller's own /proc/<getpid()>/exe lookup to /proc/self/exe.
 * No proof, kernel, evaluator, or other filesystem operation is changed.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
ssize_t readlink(const char *path, char *buf, size_t bufsiz) {
    static ssize_t (*original)(const char *, char *, size_t) = NULL;
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    char own_exe[64];
    snprintf(own_exe, sizeof own_exe, "/proc/%d/exe", (int)getpid());
    return original(strcmp(path, own_exe) == 0 ? "/proc/self/exe" : path, buf, bufsiz);
}
