// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A4: ContractType::isExplicitlyConvertibleTo (Types.cpp:1491) falls through to
// isImplicitlyConvertibleTo (Types.cpp:1475-1486), which permits a
// contract->contract conversion only when the target is in the source's
// linearized bases (an UP-cast, derived->base). A DOWN-cast (base->derived) is
// a type error.
// Pinned solc 0.8.35 rejects: "Explicit type conversion not allowed from
// \"contract Base\" to \"contract Derived\"."
contract Base {}

contract Derived is Base {}

contract A4BaseToDerived {
    function f(Base b) public pure returns (Derived) {
        return Derived(b);
    }
}
