# Building

## Build Pre-requisites

The build instructions assume you have NimSkull, latest preferred unless
otherwise noted, installed and on the path.

## Build Instructions

To get everything built, run the following from the command line

```cmd
nim c --outdir:bin -r koch.nim all
```

The above will:
- compile `koch`, the build command
- place that within the local `bin/` directory
- finally, it'll build all programs in this repository and place their
  executables in the local `bin/` directory