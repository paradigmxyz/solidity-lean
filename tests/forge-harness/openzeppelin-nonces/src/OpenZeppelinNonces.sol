// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Import-free adaptation of OpenZeppelin Contracts Nonces.
/// @dev Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.6.1/contracts/utils/Nonces.sol
abstract contract OpenZeppelinNonces {
    error InvalidAccountNonce(address account, uint256 currentNonce);

    mapping(address account => uint256) private _nonces;

    function nonces(address owner) public view virtual returns (uint256) {
        return _nonces[owner];
    }

    function _useNonce(address owner) internal virtual returns (uint256) {
        unchecked {
            return _nonces[owner]++;
        }
    }

    function _useCheckedNonce(address owner, uint256 nonce) internal virtual {
        uint256 current = _useNonce(owner);

        if (nonce != current) {
            revert InvalidAccountNonce(owner, current);
        }
    }
}

contract OpenZeppelinNoncesHarness is OpenZeppelinNonces {
    function useNonce(address owner) external returns (uint256) {
        return _useNonce(owner);
    }

    function useCheckedNonce(address owner, uint256 nonce) external {
        _useCheckedNonce(owner, nonce);
    }

    function useTwice(address owner)
        external
        returns (uint256 first, uint256 second, uint256 afterNonce)
    {
        first = _useNonce(owner);
        second = _useNonce(owner);
        afterNonce = nonces(owner);
    }
}
