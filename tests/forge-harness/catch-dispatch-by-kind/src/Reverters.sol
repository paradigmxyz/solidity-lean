// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {IReverter} from "./CatchDispatch.sol";

// Forge-side ground-truth reverters (kept out of the Lean-imported file because
// `Reverter36` needs inline assembly to revert with an exact 36-byte payload).

/// Reverts with exactly the `Error` selector + 32 zero bytes (36 bytes < 0x44).
contract Reverter36 is IReverter {
    function boom() external pure {
        assembly {
            let p := mload(0x40)
            mstore(
                p,
                0x08c379a000000000000000000000000000000000000000000000000000000000
            )
            mstore(add(p, 4), 0)
            revert(p, 36)
        }
    }
}

contract ReverterErr is IReverter {
    function boom() external pure {
        require(false, "x");
    }
}

contract ReverterPanic is IReverter {
    function boom() external pure {
        uint256 z = 0;
        uint256 r = 1 / z;
        r;
    }
}

contract ReverterCustom is IReverter {
    error Custom(uint256);

    function boom() external pure {
        revert Custom(7);
    }
}
