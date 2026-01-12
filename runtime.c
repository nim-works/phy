/// Implements the runtime for Phy-generated LLVM modules. This includes the
/// executable's entry point, as well as an implementation of the skully and
/// Phy runtime procedures.

// TODO: split this into three files:
//       * one for the LLVM runtime
//       * one for the skully runtime
//       * and one for the phy runtime

#include <stdint.h>
#include <unwind.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct PhyException {
  struct _Unwind_Exception header;
  void* data;
};

struct PhyException g_exc;
// only a single exception can be in-flight at any time

void cleanupException() {
  // the exception is part of static memory, so there's nothing to deallocate
}

void phy_raise(void* ex) {
  _Unwind_RaiseException(&g_exc.header);
  // raising the exception failed for whatever reason -> abort
  printf("internal error: raising exception failed\n");
  abort();
}

void phy_catch() {
  g_exc.data = NULL;
}

_Unwind_Reason_Code phy_eh_personality(
    int version,
    _Unwind_Action action,
    _Unwind_Exception_Class class,
    struct _Unwind_Exception * ex,
    struct _Unwind_Context * ctx) {
  // TODO: implement, or not. "Zero cost" exception handling might have zero
  //       run-time overhead (when no exception is thrown), but it sure doesn't
  //       have zero implementation cost
  return _URC_NO_REASON;
}

// ---- implementation of the skully interface

// in case of doubt, refer to the `host_impl.nim` module for how the runtime
// functions should behave

int g_argc = 0;
char** g_args = 0;

FILE* cio_getNativeStream(int64_t id) {
  switch (id) {
    case 1: return stdin;
    case 2: return stdout;
    case 3: return stderr;
  }
}

FILE* cio_fopen(const char* name, const char* mode) {
  return fopen(name, mode);
}

int cio_fclose(FILE* file) {
  return fclose(file);
}
int cio_setvbuf(FILE* f, void* buf, int mode, size_t size) {
  return setvbuf(f, buf, mode, size);
}
int cio_fflush(FILE* file) {
  return fflush(file);
}
size_t cio_fread(void* buf, size_t size, size_t n, FILE* f) {
  return fread(buf, size, n, f);
}
size_t cio_fwrite(const void* buf, size_t size, size_t n, FILE* f) {
  return fwrite(buf, size, n, f);
}
char* cio_fgets(char* c, int n, FILE* f) {
  return fgets(c, n, f);
}
int cio_fgetc(FILE* f) {
  return fgetc(f);
}
int cio_ungetc(int c, FILE* f) {
  return ungetc(c, f);
}
int cio_fseek(FILE* f, int64_t offset, int whence) {
  return fseek(f, offset, whence);
}
int cio_ftello(FILE* f) {
  return ftello(f);
}
void cio_clearerr(FILE* f) {
  clearerr(f);
}
int cio_ferror(FILE* f) {
  return ferror(f);
}
char* cstr_strerror(int errnum) {
  return strerror(errnum);
}
double cstr_strtod(const char* buf, char** endptr) {
  return strtod(buf, endptr);
}

size_t pe_paramCount() {
  return g_argc - 1;
}
size_t pe_paramStr(size_t i, void* p, size_t len) {
  // the first value in the argument array is the path/name of the program
  // itself; ignore
  i += 1;
  if (i >= 1 && i < g_argc) {
    if (p) {
      memcpy(p, g_args[i], len);
      return len;
    } else {
      // only return the required amount of space
      return strlen(g_args[i]);
    }
  } else {
    return -1;
  }
}

// ---- implementation of the core API

// the core API isn't very well-defined w.r.t. error handling. In most cases,
// we perform no error handling here

void* toCstring(const char* str, size_t len) {
  void* d = malloc(len);
  memcpy(d, str, len);
  return d;
}

size_t core_test(size_t in) {
  return in;
}
void core_write(const char* data, size_t len) {
  fwrite(data, len, 1, stdout);
}
void core_writeErr(const char* data, size_t len) {
  fwrite(data, len, 1, stderr);
}
size_t core_fileSize(const char* name, size_t len) {
  char* tmp = toCstring(name, len);
  FILE* f = fopen(tmp, "rb");
  free(tmp);
  if (f) {
    fseeko(f, 0, SEEK_END);
    off_t s = ftello(f);
    fclose(f);
    return s;
  } else {
    return 0;
  }
}
size_t core_readFile(void* dst, size_t dstLen, const char* name, size_t nameLen) {
  char* sname = toCstring(name, nameLen);
  FILE* f = fopen(sname, "rb");
  free(sname);
  if (f) {
    size_t n = fread(dst, dstLen, 1, f);
    if (ferror(f) != 0) {
      fclose(f);
      return 0;
    }
    fclose(f);
    return n;
  } else {
    return 0;
  }
}

// ---- main

extern int Main(); // the actual main function

int main(int argc, char** args) {
  g_argc = argc;
  g_args = args;
  g_exc.header.exception_cleanup = cleanupException;
  return Main();
}
