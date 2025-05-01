## Implements some generic facilities for recording arbitrary events, intended
## for performance-related instrumentation.

import std/[monotimes, times]

type
  EventKind* {.pure.} = enum
    Start ## something with a duration starts
    End ## something with a duration stops
    Action ## something with no duration happens

  Event* = object
    ## Represent something happening. Every event is associated with a timestamp.
    kind*: EventKind
      ## type of the event
    timeStamp: MonoTime
      ## when the event was recorded
    data*: string
      ## event payload

  EventLog* = object
    ## Represent an event log.
    start {.requiresInit.}: MonoTime
    events: seq[Event]

proc initLog*(): EventLog =
  ## Creates a fresh event log and sets its starting time to right now.
  EventLog(start: getMonoTime())

proc begin*(log: var EventLog, data: sink string) =
  ## Records a `Start` event with the given data.
  log.events.add Event(kind: EventKind.Start, timeStamp: getMonoTime(),
                       data: data)

proc stop*(log: var EventLog, data: sink string) =
  ## Records an `End` event with the given data.
  log.events.add Event(kind: EventKind.End, timeStamp: getMonoTime(),
                       data: data)

proc record*(log: var EventLog, data: sink string) =
  ## Records an `Action` with the given data.
  log.events.add Event(kind: EventKind.Action, timeStamp: getMonoTime(),
                       data: data)

proc relative*(log: EventLog, e: Event): Duration =
  ## Returns the time-stamp of `e` relative to when the log was started.
  e.timeStamp - log.start

proc events*(log: EventLog): lent seq[Event] =
  ## Returns the list of events.
  log.events
