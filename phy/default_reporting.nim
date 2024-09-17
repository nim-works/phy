import
  phy/reporting

type
  DefaultReporter*[T] = object of ReportContext[T]
    ## A report context that only accumulates messages, but doesn't do
    ## anything with them.
    reports: seq[T]

  FatalError*[T] = object of CatchableError
    ## Represents some error that was fatal to whoever reported it, but that
    ## can still be recovered from.
    rep*: T

proc initDefaultReporter*[T](): ref DefaultReporter[T] =
  ## Sets up a default reporter.
  new(result)
  result.sendPrc = proc(self: ref ReportContext[T], rep: sink T) =
    (ref DefaultReporter[T])(self).reports.add rep
  result.fatalPrc = proc(self: ref ReportContext[T], rep: sink T) =
    raise (ref FatalError[T])(rep: rep)

proc retrieve*[T](r: var DefaultReporter[T]): seq[T] =
  ## Takes all accumulated reports from `r`.
  result = move r.reports
