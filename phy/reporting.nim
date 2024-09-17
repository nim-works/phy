## Implements the generic reporting architecture. Everything that wants to
## report hints, warnings, or errors needs access to a ``ReportContext``-
## derived type.

import
  vm/utils

type
  ReportContext*[T] = object of RootObj
    ## The base type that all report context types must be derived from.
    debugPrc*: proc(c: ref ReportContext[T], diag: sink T)
      ## may be nil
    hintPrc*: proc(c: ref ReportContext[T], diag: sink T)
      ## may be nil
    warnPrc*: proc(c: ref ReportContext[T], diag: sink T)
      ## may be nil
    errorPrc*: proc(c: ref ReportContext[T], diag: sink T)
      ## called when an error diagnostic is sent to the context. The procedure
      ## is not required to return normally
    fatalPrc*: proc(c: ref ReportContext[T], diag: sink T)
      ## called when a fatal diagnostic is sent to the context. The procedure
      ## must not return normally

proc debug*[T](c: ref ReportContext[T], diag: sink T) =
  ## Sends the debug diagnostic `diag` to the report context.
  if c.debugPrc != nil:
    c.debugPrc(c, diag)

proc hint*[T](c: ref ReportContext[T], diag: sink T) =
  ## Sends the hint diagnostic `diag` to the report context. This is meant
  ## for user-facing hints (about some input, like code).
  if c.hintPrc != nil:
    c.hintPrc(c, diag)

proc warn*[T](c: ref ReportContext[T], diag: sink T) =
  ## Sends the error diagnostic `diag` to the report context. This is meant
  ## for user-facing warnings (about some input, like code).
  if c.warnPrc != nil:
    c.warnPrc(c, diag)

proc error*[T](c: ref ReportContext[T], diag: sink T) =
  ## Sends the error diagnostic `diag` to the report context. This is meant
  ## for user-facing errors. The callsite has to assume that ``error`` returns
  ## normally.
  c.errorPrc(c, diag)

proc fatal*[T](c: ref ReportContext[T], diag: sink T) {.noreturn.} =
  ## Sends the error diagnostic `diag` to the report context, which is
  ## guaranteed to result in the current control-flow path to terminate.
  c.fatalPrc(diag)
  unreachable()
