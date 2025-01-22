## Wraps the `Skully back-end <backend.html>`_ into a standalone compiler
## program. The compiler uses the NimSkull front-end and mid-end.

import
  std/[
    os
  ],
  compiler/front/[
    options,
    cli_reporter,
    optionsprocessor,
    condsyms,
    commands,
    cmdlinehelper,
  ],
  compiler/sem/[
    passes,
    sem,
    modulelowering
  ],
  compiler/ast/[
    idents,
    lineinfos
  ],
  compiler/modules/[
    modulegraphs,
    modules
  ],
  compiler/utils/[
    pathutils,
    platform
  ],
  compiler/backend/[
    extccomp
  ],
  passes/[
    debugutils,
    syntax,
    trees
  ],
  skully/[
    backend
  ]

proc findPatchFile(config: ConfigRef, file: string): FileIndex =
  var patchDir = getAppDir()
  # search for the directory that contains the patch modules
  if dirExists(patchDir / ".." / "skully" / "patch"):
    patchDir = patchDir / ".." / "skully" / "patch"
  elif dirExists(patchDir / "patch"):
    patchDir = patchDir / "patch"
  else:
    # give up
    raise ValueError.newException("cannot find patch directory")

  var known: bool
  result = config.fileInfoIdx(AbsoluteFile(patchDir / file), known)

proc replaceModule(config: ConfigRef, name: string, with: string) =
  var known: bool
  # this is a horrible hack, but it's the most simple and straightforward
  # solution to replacing modules at compile time not requiring modifying
  # the compiler. We register the real file and then replace its ``FileInfo``
  # with that of the module we want to replace it with
  let
    idx = config.fileInfoIdx(findModule(config, name, ""), known)
    other = findPatchFile(config, with)
  config.m.fileInfos[ord idx] = config.m.fileInfos[ord other]

proc main(args: openArray[string]) =
  if args.len != 2:
    echo args
    echo "usage: skully <module> <output>"
    quit(1)

  let config = newConfigRef(cli_reporter.reportHook)
  config.writelnHook = proc(r: ConfigRef, output: string, flags: MsgFlags) =
    stdout.writeLine(output)
  config.writeHook = proc(r: ConfigRef, output: string, flags: MsgFlags) =
    stdout.write(output)

  let
    ids   = newIdentCache()
    graph = newModuleGraph(ids, config)

  # set up a working compiler environment:
  processCmdLine(passCmd1, [], config)
  config.setFromProjectName(args[0])
  discard loadConfigs(DefaultConfig, ids, config)
  extccomp.initVars(config)
  processCmdLine(passCmd2, [], config)

  config.setFromProjectName(args[0])
  wantMainModule(config)

  # use the "any" OS in order to disable most platform-specific code
  config.target.setTarget(osAny, cpuAmd64)

  config.setDefaultLibpath()
  config.searchPathsAdd config.libpath
  defineSymbol(config, "c")
  config.exc = excGoto
  config.backend = backendC
  initDefines(config.symbols)

  # the maximum heap size is fixed at compile-time, with the possibility to
  # override the default value
  if not isDefined(config, "StandaloneHeapSize"):
    defineSymbol(config, "StandaloneHeapSize", $(1024 * 1024 * 100)) # 100 MiB

  # replace some system modules:
  replaceModule(config, "pure/os", "os.nim")

  # disable various C and platform specific code, in order to reduce the
  # amount of patching that's needed
  defineSymbol(config, "noSignalHandler") # disable default signal handlers
  defineSymbol(config, "nimNoLibc")
  defineSymbol(config, "nimEmulateOverflowChecks")
  defineSymbol(config, "nimPreviewFloatRoundtrip")
  defineSymbol(config, "noIntrinsicsBitOpts")

  config.astDiagToLegacyReport = cli_reporter.legacyReportBridge
  discard processSwitch("gc", "orc", passCmd2, config)

  # ---- the main part of compilation
  registerPass graph, semPass
  registerPass graph, collectPass

  # before compiling the main module, the various other modules skully
  # needs for operation and/or code generation have to be compiled (after
  # the system module, of course)
  graph.compileSystemModule()
  discard graph.compileModule(findPatchFile(config, "setimpl.nim"), {})
  discard graph.compileModule(findPatchFile(config, "io_helper.nim"), {})
  discard graph.compileModule(findPatchFile(config, "overrides.nim"), {})

  graph.compileProject(config.projectMainIdx)

  let m = generateCode(graph)
  writeFile(args[1], pretty(m, trees.NodeIndex(0)))

main(getExecArgs())
