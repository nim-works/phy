## Implements the allocator for the VM. The VM itself only manages the host
## memory backing the virtual memory -- heap and (to a degree) stack management
## are delegated to the guest.

type
  VirtualAddr* = distinct uint64
  ForeignRef* = distinct uint64

  HostPointer* = ptr UncheckedArray[byte]
    ## A pointer to some VM-owned memory, in the host's address space

  FreeProc = proc(p: pointer) {.nimcall, raises: [].}

  VmAllocator* = object
    ## The allocator state. The basic idea: there's only a single host
    ## allocation that backs all VM allocations. VM addresses use a virtual
    ## address space, which makes them independent from the host allocator and
    ## allows for relocating or growing the host allocation.

    # ------- host memory management
    host: HostPointer
      ## the host memory region that backs the virtual memory
    hostSize: uint
      ## current size of host memory region
    maxHost* {.requiresInit.}: uint
      ## maximum number of host memory the VM may occupy

    # ------- foreign cell management
    foreign: seq[tuple[p: pointer, rc: uint, free: FreeProc]]
      ## VM-foreign `ref` values. For empty cells, the `rc` values form an
      ## intrusive linked-list. `p` cannot be a ``RootRef``, since not foreign
      ## references aren't required to support polymorphism. As a consequence,
      ## the `free` value is required
    nextForeign: uint
      ## the next free foreign cell
    zct*: seq[ForeignRef]
      ## zero-count table. Stores all slots that have (or had) an RC of 0

const
  AddressBias* = 4096
    ## the offset applied when translating a host to a virtual address
  NilAddress* = VirtualAddr(0)
  ZctFlag = 1'u shl 63

when not defined(debug):
  {.push checks: off.}

# prevent accidental copies
proc `=copy`(a: var VmAllocator, b: VmAllocator) {.error.}

proc `==`*(a, b: VirtualAddr): bool {.borrow.}

template toVirt*(x: uint): VirtualAddr = VirtualAddr(x + AddressBias)

proc initAllocator*(initial, maxHost: uint): VmAllocator =
  assert initial < maxHost
  result = VmAllocator(maxHost: maxHost)
  # allocate the initial host memory:
  result.host = cast[HostPointer](alloc0(initial))
  result.hostSize = initial

func currSpace*(a: VmAllocator): uint =
  ## Returns the currently allocated number of bytes.
  a.hostSize

proc translate*(a: VmAllocator, p: VirtualAddr): HostPointer {.inline.} =
  ## Translate `p` to a host address. This is an *unsafe* operation, no checks
  ## are performed.
  cast[HostPointer](addr a.host[uint64(p) - AddressBias])

proc grow*(a: var VmAllocator, size: uint): bool =
  ## Grows the VM's memory to `size`. If `size` is less than the current size,
  ## or greater than the maximum allowed size, nothing changes and `false`
  ## is returned.
  if size in a.hostSize..a.maxHost:
    a.host = cast[HostPointer](realloc0(a.host, a.hostSize, size))
    a.hostSize = size
    true
  else:
    false

proc checkmem*(a: VmAllocator, address: VirtualAddr, len: uint64,
               o: var HostPointer): bool {.inline.} =
  ## * if `address` points to `len` bytes all owned by the VM, writes the host
  ##   address to `o` and returns false
  ## * otherwise leaves `o` unchanged an returns true
  let x = uint64(address)
  if likely(x >= AddressBias and x + len <= a.hostSize + AddressBias and
            x + len >= x):
    o = cast[HostPointer](addr a.host[x - AddressBias])
    false
  else:
    true # error

proc destroy[T: ref](x: pointer) =
  GC_unref cast[T](x)

proc register*[T: ref](a: var VmAllocator, r: T): ForeignRef =
  ## Register the foreign reference `r` with the allocator, returning the ID
  ## to address it with.
  if r.isNil:
    return ForeignRef(0)

  GC_ref(r)
  result = (a.nextForeign + 1).ForeignRef
  if a.nextForeign < a.foreign.len.uint:
    let next = a.foreign[a.nextForeign].rc
    a.foreign[a.nextForeign] = (cast[pointer](r), ZctFlag, destroy[T])
    a.nextForeign = next
  else:
    a.foreign.add (cast[pointer](r), ZctFlag, destroy[T])
    inc a.nextForeign

  # every new foreign ref starts off in the ZCT
  a.zct.add result

template isNonNil*(r: ForeignRef): bool =
  r.uint64 != 0

template incRef*(a: var VmAllocator, r: ForeignRef) =
  ## Increments the refcount for (valid) foreign reference `r`.
  inc a.foreign[r.uint64 - 1].rc

template decRef*(a: var VmAllocator, r: ForeignRef) =
  ## Decrement the refcount for `r`, adding it to the ZCT, if necessary.
  let s = r.uint64 - 1
  dec a.foreign[s].rc
  if a.foreign[s].rc == 0:
    a.foreign[s].rc = ZctFlag # mark as being in the ZCT
    a.zct.add ForeignRef(s+1)

proc free*(a: var VmAllocator, r: ForeignRef) =
  ## Releases the foreign reference `r`.
  let idx = r.uint64 - 1
  a.foreign[idx].free(a.foreign[idx].p)
  a.foreign[idx].p = nil
  a.foreign[idx].rc = a.nextForeign.uint
  a.nextForeign = idx.uint

proc cleanup*(a: var VmAllocator, r: ForeignRef) =
  ## Frees `r` if it's marked as being part of the ZCT and has a refcount of
  ## 0.
  let i = r.uint64 - 1
  if a.foreign[i].rc == ZctFlag:
    free(a, r)
  else:
    # non-zero refcount -> remove the ZCT flag
    a.foreign[i].rc = a.foreign[i].rc and not(ZctFlag)

template lookup*[T](a: VmAllocator, id: ForeignRef, _: typedesc[T]): T =
  # a template, to get around the lent or copy
  cast[T](a.foreign[id.int - 1].p)

template check*(a: VmAllocator, id: ForeignRef): bool =
  # the ID is biased by 1
  (id.int in 1..a.foreign.len) and a.foreign[id.int-1].p != nil
