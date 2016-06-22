module internal MurMurHash3.Alg128

[<Literal>]
let private C1 = 0x87c37b91114253d5UL
let private C2 = 0x4cf5ad432745937fUL

[<Struct>]
type private State =
  val h1 : uint64
  val h2 : uint64
  new(seed) = { h1 = seed; h2 = seed }
  new(h1,h2) = { h1 = h1; h2 = h2 }

let inline private rotL bits (o : uint64) =
  o <<< bits ||| (o >>> (64 - bits))

let inline private mixKey1 (k1 : uint64) =
  (rotL 31 (k1 * C1)) * C2

let inline private mixKey2 (k2 : uint64) =
  (rotL 33 (k2 * C2)) * C1

let inline private mixBody (state : State) k1 k2 =
  let newh1 = (rotL 27 (state.h1 ^^^ mixKey1 k1) + state.h2) * 5UL + 0x52dce729UL
  State(newh1, (rotL 31 (state.h2 ^^^ mixKey2 k2) + newh1) * 5UL + 0x38495ab5UL)

let inline private mixK (k : uint64) =
  k ^^^ (k >>> 33)

let inline private mixFinal k =
  mixK (mixK (mixK k * 0xff51afd7ed558ccdUL) * 0xc4ceb9fe1a85ec53UL)

let private finish length (state : State) =
    let h1 = state.h1 ^^^ length
    let h2 = state.h2 ^^^ length
    let h1 = h1 + h2
    let h2 = h2 + h1
    let h1 = mixFinal h1
    let h2 = mixFinal h2
    let h1 = h1 + h2
    let h2 = h2 + h1

    let returnArr : byte[] = Array.zeroCreate 16
    System.Buffer.BlockCopy(System.BitConverter.GetBytes h1, 0, returnArr, 0, 8)
    System.Buffer.BlockCopy(System.BitConverter.GetBytes h2, 0, returnArr, 8, 8)
    returnArr

module Managed =
  let inline private readULong (bytes : byte[]) offset =
        (uint64 bytes.[offset])
    ^^^ (uint64 bytes.[offset + 1] <<< 8)
    ^^^ (uint64 bytes.[offset + 2] <<< 16)
    ^^^ (uint64 bytes.[offset + 3] <<< 24)
    ^^^ (uint64 bytes.[offset + 4] <<< 32)
    ^^^ (uint64 bytes.[offset + 5] <<< 40)
    ^^^ (uint64 bytes.[offset + 6] <<< 48)
    ^^^ (uint64 bytes.[offset + 7] <<< 56)

  let rec private readPartialULong (bytes : byte[]) offset rem =
    match rem with
    | 0 -> 0UL
    | 1 -> uint64 bytes.[offset]
    | 2 ->     (uint64 bytes.[offset])
            ^^^ (uint64 bytes.[offset + 1] <<< 8)
    | 3 ->     (uint64 bytes.[offset])
            ^^^ (uint64 bytes.[offset + 1] <<< 8)
            ^^^ (uint64 bytes.[offset + 2] <<< 16)
    | 4 ->     (uint64 bytes.[offset])
            ^^^ (uint64 bytes.[offset + 1] <<< 8)
            ^^^ (uint64 bytes.[offset + 2] <<< 16)
            ^^^ (uint64 bytes.[offset + 3] <<< 24)
    | 5 ->     (uint64 bytes.[offset])
            ^^^ (uint64 bytes.[offset + 1] <<< 8)
            ^^^ (uint64 bytes.[offset + 2] <<< 16)
            ^^^ (uint64 bytes.[offset + 3] <<< 24)
            ^^^ (uint64 bytes.[offset + 4] <<< 32)
    | 6 ->     (uint64 bytes.[offset])
            ^^^ (uint64 bytes.[offset + 1] <<< 8)
            ^^^ (uint64 bytes.[offset + 2] <<< 16)
            ^^^ (uint64 bytes.[offset + 3] <<< 24)
            ^^^ (uint64 bytes.[offset + 4] <<< 32)
            ^^^ (uint64 bytes.[offset + 5] <<< 40)
    | 7 ->     (uint64 bytes.[offset])
            ^^^ (uint64 bytes.[offset + 1] <<< 8)
            ^^^ (uint64 bytes.[offset + 2] <<< 16)
            ^^^ (uint64 bytes.[offset + 3] <<< 24)
            ^^^ (uint64 bytes.[offset + 4] <<< 32)
            ^^^ (uint64 bytes.[offset + 5] <<< 40)
            ^^^ (uint64 bytes.[offset + 6] <<< 48)
    | 8 -> readULong bytes offset
    | _ -> failwith "Impossible"

  let rec private body (bytes : byte[]) len offset (state : State) =
    if offset = len then
      state
    else
      let k1 = readULong bytes offset
      let k2 = readULong bytes (offset + 8)
      body bytes len (offset + 16) (mixBody state k1 k2)

  let private last (bytes : byte[]) offset rem (state : State) =
    let k1, k2 =
      if rem < 8 then
        readPartialULong bytes offset rem, 0UL
      else
        readULong bytes offset, readPartialULong bytes (offset + 8) (rem - 8)
    State(state.h1 ^^^ mixKey1 k1, state.h2 ^^^ mixKey2 k2)

  let computeHash seed (bytes : byte[]) =
    let rem = bytes.Length &&& 15
    let len = bytes.Length &&& 0xfffffff0
    State seed
    |> body bytes len 0
    |> last bytes len rem
    |> finish (uint64 bytes.LongLength)

module Native =
  open System.Runtime.InteropServices

  let private readULongNative (offset : nativeint) =
        (uint64 (Marshal.ReadByte offset))
    ^^^ (uint64 (Marshal.ReadByte (offset + 1n)) <<< 8)
    ^^^ (uint64 (Marshal.ReadByte (offset + 2n)) <<< 16)
    ^^^ (uint64 (Marshal.ReadByte (offset + 3n)) <<< 24)
    ^^^ (uint64 (Marshal.ReadByte (offset + 4n)) <<< 32)
    ^^^ (uint64 (Marshal.ReadByte (offset + 5n)) <<< 40)
    ^^^ (uint64 (Marshal.ReadByte (offset + 6n)) <<< 48)
    ^^^ (uint64 (Marshal.ReadByte (offset + 7n)) <<< 56)


  let rec private readPartialULongNative (offset : nativeint) (rem : nativeint) =
    match rem with
    | 0n -> 0UL
    | 1n -> uint64 (Marshal.ReadByte offset)
    | 2n ->     (uint64 (Marshal.ReadByte offset))
            ^^^ (uint64 (Marshal.ReadByte (offset + 1n)) <<< 8)
    | 3n ->     (uint64 (Marshal.ReadByte offset))
            ^^^ (uint64 (Marshal.ReadByte (offset + 1n)) <<< 8)
            ^^^ (uint64 (Marshal.ReadByte (offset + 2n)) <<< 16)
    | 4n ->     (uint64 (Marshal.ReadByte offset))
            ^^^ (uint64 (Marshal.ReadByte (offset + 1n)) <<< 8)
            ^^^ (uint64 (Marshal.ReadByte (offset + 2n)) <<< 16)
            ^^^ (uint64 (Marshal.ReadByte (offset + 3n)) <<< 24)
    | 5n ->     (uint64 (Marshal.ReadByte offset))
            ^^^ (uint64 (Marshal.ReadByte (offset + 1n)) <<< 8)
            ^^^ (uint64 (Marshal.ReadByte (offset + 2n)) <<< 16)
            ^^^ (uint64 (Marshal.ReadByte (offset + 3n)) <<< 24)
            ^^^ (uint64 (Marshal.ReadByte (offset + 4n)) <<< 32)
    | 6n ->     (uint64 (Marshal.ReadByte offset))
            ^^^ (uint64 (Marshal.ReadByte (offset + 1n)) <<< 8)
            ^^^ (uint64 (Marshal.ReadByte (offset + 2n)) <<< 16)
            ^^^ (uint64 (Marshal.ReadByte (offset + 3n)) <<< 24)
            ^^^ (uint64 (Marshal.ReadByte (offset + 4n)) <<< 32)
            ^^^ (uint64 (Marshal.ReadByte (offset + 5n)) <<< 40)
    | 7n ->     (uint64 (Marshal.ReadByte offset))
            ^^^ (uint64 (Marshal.ReadByte (offset + 1n)) <<< 8)
            ^^^ (uint64 (Marshal.ReadByte (offset + 2n)) <<< 16)
            ^^^ (uint64 (Marshal.ReadByte (offset + 3n)) <<< 24)
            ^^^ (uint64 (Marshal.ReadByte (offset + 4n)) <<< 32)
            ^^^ (uint64 (Marshal.ReadByte (offset + 5n)) <<< 40)
            ^^^ (uint64 (Marshal.ReadByte (offset + 6n)) <<< 48)
    | 8n -> readULongNative offset
    | _  -> failwith "Impossible"

  let rec private body (stop : nativeint) (offset : nativeint) (state : State) =
    if offset = stop then
      state
    else
      let k1 = uint64 (readULongNative offset)
      let k2 = uint64 (readULongNative (offset + 8n))
      body stop (offset + 16n) (mixBody state k1 k2)

  let private last (offset : nativeint) (rem : nativeint) (state : State) =
    let k =
      if rem < 8n then
        State(readPartialULongNative offset rem, 0UL)
      else
        State(readULongNative offset, readPartialULongNative (offset + 8n) (rem - 8n))
    State(state.h1 ^^^ mixKey1 k.h1, state.h2 ^^^ mixKey2 k.h2)

  let computeHash seed (bytes : byte[]) =
    let length = (uint64 bytes.LongLength)
    let gch = GCHandle.Alloc(bytes, GCHandleType.Pinned)
    try
      let rem = length &&& 15UL |> nativeint
      let len = length &&& 0xfffffffffffffff0UL |> nativeint
      let offset = gch.AddrOfPinnedObject()
      let stop = offset + len
      State seed
      |> body stop offset
      |> last stop rem
      |> finish length
    finally
      gch.Free()
