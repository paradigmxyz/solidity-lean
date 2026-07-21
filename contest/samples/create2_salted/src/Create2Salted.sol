// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// CONTRACT CREATION is explicitly OUT OF SCOPE in v1 (X-EXTCALL): a creation
// executes an external deployment sub-context and its outcome (created/CREATE2
// address on success; revert on a constructor revert / occupied address) needs
// the v2 responder. This sample uses the salted CREATE2 form. Child is also a
// BASE of the entry contract, so V1-MULTI stays quiet (a base is not a
// separately-deployable contract) and the verdict isolates the creation
// exclusions. It must land as a CLEAN REJECTED_OOS — never an incidental
// address-0 revert or a NEEDS_REVIEW. SEM-ADDR also fires (a salted create2
// predicted address flowing to the observed return).
contract Child {
    uint256 public x;
}

contract Create2Salted is Child {
    function make(uint256 salt) external returns (address) {
        return address(new Child{salt: bytes32(salt)}());
    }
}
