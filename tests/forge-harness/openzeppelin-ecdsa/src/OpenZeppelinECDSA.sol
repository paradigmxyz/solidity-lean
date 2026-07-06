// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-free, assembly-free adaptation of selected OpenZeppelin Contracts
// v5.6.1 ECDSA paths. The bytes/bytes calldata signature parsing overloads
// and parse helpers are intentionally omitted because upstream implements them
// with inline assembly/Yul; this slice keeps the Solidity-level v/r/s and
// ERC-2098 r/vs recovery semantics.
library OpenZeppelinECDSA {
    enum RecoverError {
        NoError,
        InvalidSignature,
        InvalidSignatureLength,
        InvalidSignatureS
    }

    error ECDSAInvalidSignature();
    error ECDSAInvalidSignatureLength(uint256 length);
    error ECDSAInvalidSignatureS(bytes32 s);

    function tryRecover(bytes32 hash, bytes32 r, bytes32 vs)
        internal
        pure
        returns (address recovered, RecoverError err, bytes32 errArg)
    {
        unchecked {
            bytes32 s =
                vs & bytes32(
                    0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                );
            uint8 v = uint8((uint256(vs) >> 255) + 27);
            return tryRecover(hash, v, r, s);
        }
    }

    function recover(bytes32 hash, bytes32 r, bytes32 vs)
        internal
        pure
        returns (address)
    {
        (address recovered, RecoverError recoverError, bytes32 errorArg) =
            tryRecover(hash, r, vs);
        _throwError(recoverError, errorArg);
        return recovered;
    }

    function tryRecover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    )
        internal
        pure
        returns (address recovered, RecoverError err, bytes32 errArg)
    {
        if (
            uint256(s) >
            0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0
        ) {
            return (address(0), RecoverError.InvalidSignatureS, s);
        }

        address signer = ecrecover(hash, v, r, s);
        if (signer == address(0)) {
            return (
                address(0),
                RecoverError.InvalidSignature,
                bytes32(0)
            );
        }

        return (signer, RecoverError.NoError, bytes32(0));
    }

    function recover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal pure returns (address) {
        (address recovered, RecoverError recoverError, bytes32 errorArg) =
            tryRecover(hash, v, r, s);
        _throwError(recoverError, errorArg);
        return recovered;
    }

    function _throwError(RecoverError recoverError, bytes32 errorArg) private pure {
        if (recoverError == RecoverError.NoError) {
            return;
        } else if (recoverError == RecoverError.InvalidSignature) {
            revert ECDSAInvalidSignature();
        } else if (recoverError == RecoverError.InvalidSignatureLength) {
            revert ECDSAInvalidSignatureLength(uint256(errorArg));
        } else if (recoverError == RecoverError.InvalidSignatureS) {
            revert ECDSAInvalidSignatureS(errorArg);
        }
    }
}

contract OpenZeppelinECDSAHarness {
    using OpenZeppelinECDSA for bytes32;

    function tryRecoverVRS(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    )
        external
        pure
        returns (
            address recovered,
            OpenZeppelinECDSA.RecoverError err,
            bytes32 errArg
        )
    {
        (address signer, OpenZeppelinECDSA.RecoverError recoverError, bytes32 arg) =
            OpenZeppelinECDSA.tryRecover(hash, v, r, s);
        return (signer, recoverError, arg);
    }

    function recoverVRS(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external pure returns (address) {
        return OpenZeppelinECDSA.recover(hash, v, r, s);
    }

    function tryRecoverShort(bytes32 hash, bytes32 r, bytes32 vs)
        external
        pure
        returns (
            address recovered,
            OpenZeppelinECDSA.RecoverError err,
            bytes32 errArg
        )
    {
        (address signer, OpenZeppelinECDSA.RecoverError recoverError, bytes32 arg) =
            OpenZeppelinECDSA.tryRecover(hash, r, vs);
        return (signer, recoverError, arg);
    }

    function recoverShort(bytes32 hash, bytes32 r, bytes32 vs)
        external
        pure
        returns (address)
    {
        return OpenZeppelinECDSA.recover(hash, r, vs);
    }

    function recoverUsingFor(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external pure returns (address) {
        return hash.recover(v, r, s);
    }

    function halfOrderLimit() external pure returns (bytes32) {
        return bytes32(
            0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0
        );
    }
}
