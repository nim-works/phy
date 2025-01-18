This directory contains:
* modified versions of various system / platform-specific modules. When using
  `skully`, imports of the original modules are automatically redirected to the
  modified versions
* the compiler runtime use by Skully's code generator
* additional modules injected into the compilation in order to alter some
  global state at program startup
