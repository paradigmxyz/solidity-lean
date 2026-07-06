// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Import-free adaptation of OpenZeppelin Contracts Nonces and NoncesKeyed.
/// @dev Sources:
/// https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.6.1/contracts/utils/Nonces.sol
/// https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.6.1/contracts/utils/NoncesKeyed.sol
/// The derived private keyed mapping is alpha-renamed from upstream `_nonces`
/// to `_keyedNonces`; Solidity treats the two inherited private declarations
/// as distinct, while this abstract executable currently keys storage by name.
abstract contract OpenZeppelinNoncesKeyedBase {
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

abstract contract OpenZeppelinNoncesKeyed is OpenZeppelinNoncesKeyedBase {
    mapping(address owner => mapping(uint192 key => uint64)) private
        _keyedNonces;

    function nonces(address owner, uint192 key)
        public
        view
        virtual
        returns (uint256)
    {
        return key == 0 ? nonces(owner) : _pack(key, _keyedNonces[owner][key]);
    }

    function _useNonce(address owner, uint192 key)
        internal
        virtual
        returns (uint256)
    {
        unchecked {
            return key == 0
                ? _useNonce(owner)
                : _pack(key, _keyedNonces[owner][key]++);
        }
    }

    function _useCheckedNonce(address owner, uint256 keyNonce)
        internal
        virtual
        override
    {
        (uint192 key, ) = _unpack(keyNonce);
        if (key == 0) {
            super._useCheckedNonce(owner, keyNonce);
        } else {
            uint256 current = _useNonce(owner, key);
            if (keyNonce != current) {
                revert InvalidAccountNonce(owner, current);
            }
        }
    }

    function _useCheckedNonce(address owner, uint192 key, uint64 nonce)
        internal
        virtual
    {
        _useCheckedNonce(owner, _pack(key, nonce));
    }

    function _pack(uint192 key, uint64 nonce) private pure returns (uint256) {
        return (uint256(key) << 64) | nonce;
    }

    function _unpack(uint256 keyNonce)
        private
        pure
        returns (uint192 key, uint64 nonce)
    {
        return (uint192(keyNonce >> 64), uint64(keyNonce));
    }
}

contract OpenZeppelinNoncesKeyedHarness is OpenZeppelinNoncesKeyed {
    function useNonce(address owner) external returns (uint256) {
        return _useNonce(owner);
    }

    function useNonceWithKey(address owner, uint192 key)
        external
        returns (uint256)
    {
        return _useNonce(owner, key);
    }

    function useCheckedNoncePacked(address owner, uint256 keyNonce) external {
        uint192 key = uint192(keyNonce >> 64);
        uint256 current = key == 0 ? _useNonce(owner) : _useNonce(owner, key);
        if (keyNonce != current) {
            revert InvalidAccountNonce(owner, current);
        }
    }

    function useCheckedNonceSplit(address owner, uint192 key, uint64 nonce)
        external
    {
        uint256 keyNonce = (uint256(key) << 64) | nonce;
        uint256 current = key == 0 ? _useNonce(owner) : _useNonce(owner, key);
        if (keyNonce != current) {
            revert InvalidAccountNonce(owner, current);
        }
    }

    function useKeyedTwice(address owner, uint192 key)
        external
        returns (uint256 first, uint256 second, uint256 afterNonce)
    {
        first = _useNonce(owner, key);
        second = _useNonce(owner, key);
        afterNonce = nonces(owner, key);
    }

    function packForTest(uint192 key, uint64 nonce)
        external
        pure
        returns (uint256)
    {
        return (uint256(key) << 64) | nonce;
    }

    function unpackForTest(uint256 keyNonce)
        external
        pure
        returns (uint192 key, uint64 nonce)
    {
        return (uint192(keyNonce >> 64), uint64(keyNonce));
    }
}
