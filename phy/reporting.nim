## Implements the generic reporting architecture. Everything that wants to
## report hints, warnings, or errors needs access to a ``ReportContext``-
## derived type.

import
  vm/utils

type
  ReportContext*[T] = object of RootObj
    ## The base type that all report context types must be derived from.
    sendPrc*: proc(c: ref ReportContext[T], rep: sink T)
      ## called when a message is sent to the context
    fatalPrc*: proc(c: ref ReportContext[T], rep: sink T)
      ## called when a fatal message is sent to the context. The procedure
      ## must not return normally

proc report*[T](c: ref ReportContext[T], rep: sink T) =
  ## Sends `rep` to the report context.
  c.sendPrc(c, rep)

proc fatal*[T](c: ref ReportContext[T], rep: sink T) {.noreturn.} =
  ## Sends `rep` to the report context, which is guaranteed to result in the
  ## current control-flow path to terminate.
  c.fatalPrc(rep)
  unreachable()
