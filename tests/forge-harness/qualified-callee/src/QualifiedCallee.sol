// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// QUAL-CALLEE (#74 / #77): emit and revert / require whose callee is a MEMBER
// access (`Base.BaseHit`, `Base.BaseErr`, self `C.LocalHit`, `C.LocalErr`)
// rather than a bare identifier. solc 0.8.35 accepts these; solidity-lean
// previously over-rejected them (emit at the executable lowering, revert /
// require at the type checker AND the lowering). Only base-/self-qualified
// callees whose event/error is in the contract's flattened scope are closed;
// library-/interface-qualified errors (`L.Bad`) remain declined.

contract Base {
    event BaseHit(uint256 value);
    error BaseErr(uint256 value);
}

contract QualifiedCalleeHarnessTarget is Base {
    event LocalHit(uint256 value);
    error LocalErr(uint256 value);

    // emit Base.E(a) — base-contract-qualified event.
    function emitBaseHit(uint256 value) external {
        emit Base.BaseHit(value);
    }

    // emit C.E(a) — self-qualified event.
    function emitSelfHit(uint256 value) external {
        emit QualifiedCalleeHarnessTarget.LocalHit(value);
    }

    // revert Base.Err(a) — inherited/base-qualified custom error.
    function revertBaseErr(uint256 value) external pure {
        revert Base.BaseErr(value);
    }

    // revert C.Err(a) — self-qualified custom error.
    function revertSelfErr(uint256 value) external pure {
        revert QualifiedCalleeHarnessTarget.LocalErr(value);
    }

    // require(cond, Base.Err(a)) — require form with a base-qualified error.
    function requireBaseErr(uint256 value) external pure {
        require(value > 0, Base.BaseErr(value));
    }
}
