// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// #54 (MOD-RET): the same rejection for `return require(true);` — a void-typed
// call argument inside a modifier body (TypeError 7552).
contract ModifierReturnRequire {
    modifier m() {
        return require(true);
        _;
    }
    function f() public m {}
}
