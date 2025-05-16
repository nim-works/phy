# Building

## Build Pre-requisites

The build instructions assume you have NimSkull installed and on the path,
with the minimum required version found [here](https://github.com/nim-works/phy/blob/main/nimskull.version#L1).

> Important: the `skully` program imports internal compiler modules, which
> means that using a more recent compiler version might cause the program to
> not work correctly.

## Build Instructions

To get everything built, run the following from the command line

```cmd
nim c --outdir:bin -r koch.nim build all
```

The above will:
- compile `koch`, the build command
- place that within the local `bin/` directory
- finally, it'll build all programs in this repository and place their
  executables in the local `bin/` directory
