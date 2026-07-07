#!/bin/zsh
# helper: run a single probe by tag (one lean job at a time). NOT committed.
cd /Users/dan/Projects/solid-core-spine-audit
D=tests/bc-audit-probes
RV='let rv := (fun (r:CallResult) => match r with | .returned _ vs => vs | .reverted _ _ => []);'
case "$1" in
transientmix)
 python3 $D/drive.py eval $D/c-features/TransientMix.sol TransientMix \
 "(toString (repr ((do $RV let r <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"setBoth\") State.empty [Value.word 7, Value.word 9]; pure (rv r, r.resultState.storage, r.resultState.transient)) : Except TypeError _)))" ;;
constimm)
 python3 $D/drive.py eval $D/c-features/ConstImm.sol ConstImm \
 "(toString (repr ((do $RV let c <- CheckedInput.ownConstruct 32 importedContract State.empty [Value.word 5]; let g2 <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getC2\") c.resultState []; let i1 <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getI1\") c.resultState []; let i2 <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getI2\") c.resultState []; pure (rv g2, rv i1, rv i2)) : Except TypeError _)))" ;;
diamond)
 python3 $D/drive.py eval $D/c-features/Diamond.sol D \
 "(toString (repr ((do $RV let c <- CheckedInput.ownConstruct 32 importedContract State.empty []; let g <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getLog\") c.resultState []; let w <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"who\") c.resultState []; pure (rv g, rv w, c.resultState.storage)) : Except TypeError _)))" ;;
trycatch)
 python3 $D/drive.py eval $D/c-features/TryCatch.sol TryCatch \
 "(toString (repr ((do $RV let c <- CheckedInput.ownConstruct 32 importedContract State.empty []; let r0 <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"run\") c.resultState [Value.word 0]; let r1 <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"run\") c.resultState [Value.word 1]; let r2 <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"run\") c.resultState [Value.word 2]; pure (rv r0, rv r1, rv r2)) : Except TypeError _)))" ;;
freefn)
 python3 $D/drive.py eval $D/c-features/FreeFn.sol FreeFn \
 'Examples.checkedOwnCallWordMatches 32 importedContract "useFree" State.empty [Value.word 3, Value.word 4] 19' ;;
delete)
 python3 $D/drive.py eval $D/b6-storage/DeleteAgg.sol DeleteAgg \
 "(toString (repr ((do $RV let s <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"setup\") State.empty []; let ds <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"delStruct\") s.resultState []; let a <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getSA\") ds.resultState []; let b <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getSB\") ds.resultState []; let l <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getSArrLen\") ds.resultState []; pure (rv a, rv b, rv l)) : Except TypeError _)))" \
 "(toString (repr ((do $RV let s <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"setup\") State.empty []; let de <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"delArrElem\") s.resultState []; let x0 <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getXs\") de.resultState [Value.word 0]; let x1 <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getXs\") de.resultState [Value.word 1]; let l <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getXsLen\") de.resultState []; pure (rv x0, rv x1, rv l)) : Except TypeError _)))" \
 "(toString (repr ((do $RV let s <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"setup\") State.empty []; let p <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"popArr\") s.resultState []; let l <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getXsLen\") p.resultState []; let dm <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"delMapKey\") s.resultState []; let m <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getM\") dm.resultState [Value.word 5]; pure (rv l, rv m)) : Except TypeError _)))" ;;
bytesstr)
 # strings of length 30,31,32,33 as calldata bytes (Value.bytes list of Byte)
 mk() { python3 -c "print('[' + ', '.join(['0x41']*$1) + ']')"; }  # 'A' repeated
 L30=$(mk 30); L31=$(mk 31); L32=$(mk 32); L33=$(mk 33)
 python3 $D/drive.py eval $D/b6-storage/BytesStr.sol BytesStr \
 "(toString (repr ((do $RV let r <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"setStr\") State.empty [Value.bytes $L30]; let l <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getStrLen\") r.resultState []; pure (rv l, r.resultState.storage)) : Except TypeError _)))" \
 "(toString (repr ((do $RV let r <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"setStr\") State.empty [Value.bytes $L31]; let l <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getStrLen\") r.resultState []; pure (rv l, r.resultState.storage)) : Except TypeError _)))" \
 "(toString (repr ((do $RV let r <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"setStr\") State.empty [Value.bytes $L32]; let l <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getStrLen\") r.resultState []; pure (rv l, r.resultState.storage)) : Except TypeError _)))" \
 "(toString (repr ((do $RV let r <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"setStr\") State.empty [Value.bytes $L33]; let l <- CheckedInput.ownCall 32 importedContract (CallTarget.name \"getStrLen\") r.resultState []; pure (rv l, r.resultState.storage)) : Except TypeError _)))" ;;
esac
