// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// A1 divergence lane: `type(T).interfaceId` is exposed by solc for any
// NON-deployable contract — an interface OR an abstract contract
// (Types.cpp:4271-4285) — and equals the XOR of the 4-byte selectors of
// `interfaceFunctionList(false)`: the externally-visible functions AND public
// state-variable getters DECLARED DIRECTLY in the contract (AST.cpp:315-321).
// Internal/private functions are excluded. A concrete deployable contract has no
// `.interfaceId` member (see invalid/ConcreteInterfaceId.sol).
abstract contract AbstractLedger {
    uint256 public totalSupply;                                  // getter -> counts

    function transfer(address to, uint256 amount)
        external
        virtual
        returns (bool);

    function balanceOf(address account)
        external
        view
        virtual
        returns (uint256);

    function _settle(uint256 x) internal virtual returns (uint256); // excluded
}

contract AbstractInterfaceIdHarnessTarget {
    function abstractLedgerId() external pure returns (bytes4) {
        return type(AbstractLedger).interfaceId;
    }
}
