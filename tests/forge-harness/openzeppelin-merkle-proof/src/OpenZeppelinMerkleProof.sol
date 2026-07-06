// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

// Import-inlined, assembly-free adaptation of OpenZeppelin Contracts v4.9.6
// `utils/cryptography/MerkleProof.sol`. The upstream `_efficientHash` helper
// uses inline assembly only as an optimization; this source-semantics fixture
// keeps the same Solidity-level hash meaning with `keccak256(abi.encodePacked)`.
library OpenZeppelinMerkleProof {
    function verify(bytes32[] memory proof, bytes32 root, bytes32 leaf)
        internal
        pure
        returns (bool)
    {
        return processProof(proof, leaf) == root;
    }

    function verifyCalldata(
        bytes32[] calldata proof,
        bytes32 root,
        bytes32 leaf
    ) internal pure returns (bool) {
        return processProofCalldata(proof, leaf) == root;
    }

    function processProof(bytes32[] memory proof, bytes32 leaf)
        internal
        pure
        returns (bytes32)
    {
        bytes32 computedHash = leaf;
        for (uint256 i = 0; i < proof.length; i++) {
            computedHash = _hashPair(computedHash, proof[i]);
        }
        return computedHash;
    }

    function processProofCalldata(bytes32[] calldata proof, bytes32 leaf)
        internal
        pure
        returns (bytes32)
    {
        bytes32 computedHash = leaf;
        for (uint256 i = 0; i < proof.length; i++) {
            computedHash = _hashPair(computedHash, proof[i]);
        }
        return computedHash;
    }

    function multiProofVerify(
        bytes32[] memory proof,
        bool[] memory proofFlags,
        bytes32 root,
        bytes32[] memory leaves
    ) internal pure returns (bool) {
        return processMultiProof(proof, proofFlags, leaves) == root;
    }

    function multiProofVerifyCalldata(
        bytes32[] calldata proof,
        bool[] calldata proofFlags,
        bytes32 root,
        bytes32[] memory leaves
    ) internal pure returns (bool) {
        return processMultiProofCalldata(proof, proofFlags, leaves) == root;
    }

    function processMultiProof(
        bytes32[] memory proof,
        bool[] memory proofFlags,
        bytes32[] memory leaves
    ) internal pure returns (bytes32 merkleRoot) {
        uint256 leavesLen = leaves.length;
        uint256 proofLen = proof.length;
        uint256 totalHashes = proofFlags.length;

        require(
            leavesLen + proofLen - 1 == totalHashes,
            "MerkleProof: invalid multiproof"
        );

        bytes32[] memory hashes = new bytes32[](totalHashes);
        uint256 leafPos = 0;
        uint256 hashPos = 0;
        uint256 proofPos = 0;

        for (uint256 i = 0; i < totalHashes; i++) {
            bytes32 a = leafPos < leavesLen
                ? leaves[leafPos++]
                : hashes[hashPos++];
            bytes32 b = proofFlags[i]
                ? (
                    leafPos < leavesLen
                        ? leaves[leafPos++]
                        : hashes[hashPos++]
                )
                : proof[proofPos++];
            hashes[i] = _hashPair(a, b);
        }

        if (totalHashes > 0) {
            require(
                proofPos == proofLen,
                "MerkleProof: invalid multiproof"
            );
            unchecked {
                return hashes[totalHashes - 1];
            }
        } else if (leavesLen > 0) {
            return leaves[0];
        } else {
            return proof[0];
        }
    }

    function processMultiProofCalldata(
        bytes32[] calldata proof,
        bool[] calldata proofFlags,
        bytes32[] memory leaves
    ) internal pure returns (bytes32 merkleRoot) {
        uint256 leavesLen = leaves.length;
        uint256 proofLen = proof.length;
        uint256 totalHashes = proofFlags.length;

        require(
            leavesLen + proofLen - 1 == totalHashes,
            "MerkleProof: invalid multiproof"
        );

        bytes32[] memory hashes = new bytes32[](totalHashes);
        uint256 leafPos = 0;
        uint256 hashPos = 0;
        uint256 proofPos = 0;

        for (uint256 i = 0; i < totalHashes; i++) {
            bytes32 a = leafPos < leavesLen
                ? leaves[leafPos++]
                : hashes[hashPos++];
            bytes32 b = proofFlags[i]
                ? (
                    leafPos < leavesLen
                        ? leaves[leafPos++]
                        : hashes[hashPos++]
                )
                : proof[proofPos++];
            hashes[i] = _hashPair(a, b);
        }

        if (totalHashes > 0) {
            require(
                proofPos == proofLen,
                "MerkleProof: invalid multiproof"
            );
            unchecked {
                return hashes[totalHashes - 1];
            }
        } else if (leavesLen > 0) {
            return leaves[0];
        } else {
            return proof[0];
        }
    }

    function hashPairForHarness(bytes32 a, bytes32 b)
        internal
        pure
        returns (bytes32)
    {
        return _hashPair(a, b);
    }

    function _hashPair(bytes32 a, bytes32 b)
        private
        pure
        returns (bytes32)
    {
        if (a < b) {
            return keccak256(abi.encodePacked(a, b));
        } else {
            return keccak256(abi.encodePacked(b, a));
        }
    }
}

contract OpenZeppelinMerkleProofHarness {
    function verifyMemory(
        bytes32[] memory proof,
        bytes32 root,
        bytes32 leaf
    ) external pure returns (bool) {
        return OpenZeppelinMerkleProof.verify(proof, root, leaf);
    }

    function verifyCalldata(
        bytes32[] calldata proof,
        bytes32 root,
        bytes32 leaf
    ) external pure returns (bool) {
        return OpenZeppelinMerkleProof.verifyCalldata(proof, root, leaf);
    }

    function processMemory(bytes32[] memory proof, bytes32 leaf)
        external
        pure
        returns (bytes32)
    {
        return OpenZeppelinMerkleProof.processProof(proof, leaf);
    }

    function processCalldata(bytes32[] calldata proof, bytes32 leaf)
        external
        pure
        returns (bytes32)
    {
        return OpenZeppelinMerkleProof.processProofCalldata(proof, leaf);
    }

    function multiProofMemory(
        bytes32[] memory proof,
        bool[] memory proofFlags,
        bytes32[] memory leaves
    ) external pure returns (bytes32) {
        return OpenZeppelinMerkleProof.processMultiProof(
            proof,
            proofFlags,
            leaves
        );
    }

    function multiProofCalldata(
        bytes32[] calldata proof,
        bool[] calldata proofFlags,
        bytes32[] memory leaves
    ) external pure returns (bytes32) {
        return OpenZeppelinMerkleProof.processMultiProofCalldata(
            proof,
            proofFlags,
            leaves
        );
    }

    function multiVerifyMemory(
        bytes32[] memory proof,
        bool[] memory proofFlags,
        bytes32 root,
        bytes32[] memory leaves
    ) external pure returns (bool) {
        return OpenZeppelinMerkleProof.multiProofVerify(
            proof,
            proofFlags,
            root,
            leaves
        );
    }

    function multiVerifyCalldata(
        bytes32[] calldata proof,
        bool[] calldata proofFlags,
        bytes32 root,
        bytes32[] memory leaves
    ) external pure returns (bool) {
        return OpenZeppelinMerkleProof.multiProofVerifyCalldata(
            proof,
            proofFlags,
            root,
            leaves
        );
    }

    function pairHash(bytes32 a, bytes32 b) external pure returns (bytes32) {
        return OpenZeppelinMerkleProof.hashPairForHarness(a, b);
    }

    function less(bytes32 a, bytes32 b) external pure returns (bool) {
        return a < b;
    }
}
