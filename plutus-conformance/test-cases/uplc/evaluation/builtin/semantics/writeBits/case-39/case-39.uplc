-- Check that indices don't wrap around
(program 1.0.0
 [
  [
   [
    (builtin writeBits)
    (con bytestring #33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0)
   ]
   (con (list integer) [-9223372036854775809])  -- (minBound :: Int) - 1
  ]
  (con (list bool) [True])
 ]
)
