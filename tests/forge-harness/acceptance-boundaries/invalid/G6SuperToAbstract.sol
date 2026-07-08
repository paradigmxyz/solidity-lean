// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// G6: `super.f()` resolving to an abstract (unimplemented) base — solc TypeError 9582.
abstract contract G6Base {
    function f() public view virtual returns (uint);
}

contract G6Derived is G6Base {
    function f() public view virtual override returns (uint) {
        return super.f();
    }
}
