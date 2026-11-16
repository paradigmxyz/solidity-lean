#!/usr/bin/env bash
# usage: lake_ab.sh <label>: rebuild KernelRfl's importers under the current lakefile, timed
source ~/env.sh; cd ~/bench/sl
rm -f .lake/build/lib/lean/flag_4ce5cf9a/{Lowering,SpecConnect}.olean .lake/build/lib/lean/SolidCore/Refinement/{Kernel,KernelRfl,KernelCopies}.olean
~/bench/harness/memtime.py ~/bench/ab/lake_$1.time ~/bench/slot.sh lake -R build -KleanMemory=9000 flag_4ce5cf9a.SpecConnect > ~/bench/ab/lake_$1.full 2>&1
echo "$1 exit $?"; grep -E 'Built (SolidCore.Refinement.Kernel|flag_4ce5cf9a|SolidCoreKernel)' ~/bench/ab/lake_$1.full | sed 's/^[^]]*] //'; grep Elapsed ~/bench/ab/lake_$1.time; sha256sum .lake/build/lib/lean/flag_4ce5cf9a/{Lowering,SpecConnect}.olean | cut -c1-16
