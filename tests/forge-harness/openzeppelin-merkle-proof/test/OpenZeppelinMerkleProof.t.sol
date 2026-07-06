// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {
    OpenZeppelinMerkleProofHarness
} from "../src/OpenZeppelinMerkleProof.sol";

contract OpenZeppelinMerkleProofForgeTest {
    function pair(bytes32 a, bytes32 b) internal pure returns (bytes32) {
        return a < b
            ? keccak256(abi.encodePacked(a, b))
            : keccak256(abi.encodePacked(b, a));
    }

    function leaves()
        internal
        pure
        returns (bytes32 a, bytes32 b, bytes32 c, bytes32 d)
    {
        return (
            bytes32(uint256(0x11)),
            bytes32(uint256(0x22)),
            bytes32(uint256(0x33)),
            bytes32(uint256(0x44))
        );
    }

    function proofForFirstLeaf()
        internal
        pure
        returns (bytes32[] memory proof, bytes32 root, bytes32 leaf)
    {
        (bytes32 a, bytes32 b, bytes32 c, bytes32 d) = leaves();
        bytes32 h01 = pair(a, b);
        bytes32 h23 = pair(c, d);
        root = pair(h01, h23);
        leaf = a;
        proof = new bytes32[](2);
        proof[0] = b;
        proof[1] = h23;
    }

    function multiProofForRightBranch()
        internal
        pure
        returns (
            bytes32[] memory proof,
            bool[] memory flags,
            bytes32[] memory branchLeaves,
            bytes32 root
        )
    {
        (bytes32 a, bytes32 b, bytes32 c, bytes32 d) = leaves();
        bytes32 h01 = pair(a, b);
        bytes32 h23 = pair(c, d);
        root = pair(h01, h23);

        proof = new bytes32[](1);
        proof[0] = h01;
        flags = new bool[](2);
        flags[0] = true;
        flags[1] = false;
        branchLeaves = new bytes32[](2);
        branchLeaves[0] = c;
        branchLeaves[1] = d;
    }

    function testSingleProofMemoryAndCalldata() public {
        OpenZeppelinMerkleProofHarness target =
            new OpenZeppelinMerkleProofHarness();
        (bytes32[] memory proof, bytes32 root, bytes32 leaf) =
            proofForFirstLeaf();
        (, bytes32 sibling, , ) = leaves();

        require(target.less(leaf, sibling), "leaf less sibling");
        require(!target.less(sibling, leaf), "sibling not less leaf");
        require(target.pairHash(sibling, leaf) == pair(leaf, sibling), "sort");
        require(target.processMemory(proof, leaf) == root, "process memory");
        require(target.verifyMemory(proof, root, leaf), "verify memory");
        require(
            target.processCalldata(proof, leaf) == root,
            "process calldata"
        );
        require(target.verifyCalldata(proof, root, leaf), "verify calldata");
        require(
            !target.verifyMemory(proof, root, bytes32(uint256(0x99))),
            "wrong leaf"
        );
    }

    function testMultiProofMemoryAndCalldata() public {
        OpenZeppelinMerkleProofHarness target =
            new OpenZeppelinMerkleProofHarness();
        (
            bytes32[] memory proof,
            bool[] memory flags,
            bytes32[] memory branchLeaves,
            bytes32 root
        ) = multiProofForRightBranch();

        require(
            target.multiProofMemory(proof, flags, branchLeaves) == root,
            "multi memory"
        );
        require(
            target.multiVerifyMemory(proof, flags, root, branchLeaves),
            "multi verify memory"
        );
        require(
            target.multiProofCalldata(proof, flags, branchLeaves) == root,
            "multi calldata"
        );
        require(
            target.multiVerifyCalldata(proof, flags, root, branchLeaves),
            "multi verify calldata"
        );
    }

    function testEmptyLeavesMultiproofReturnsOnlyProofNode() public {
        OpenZeppelinMerkleProofHarness target =
            new OpenZeppelinMerkleProofHarness();
        bytes32[] memory proof = new bytes32[](1);
        proof[0] = bytes32(uint256(0xabc));
        bool[] memory flags = new bool[](0);
        bytes32[] memory emptyLeaves = new bytes32[](0);

        require(
            target.multiProofMemory(proof, flags, emptyLeaves) == proof[0],
            "single proof root"
        );
        require(
            target.multiVerifyMemory(proof, flags, proof[0], emptyLeaves),
            "single proof verify"
        );
    }

    function testInvalidMultiproofReverts() public {
        OpenZeppelinMerkleProofHarness target =
            new OpenZeppelinMerkleProofHarness();
        bytes32[] memory proof = new bytes32[](1);
        proof[0] = bytes32(uint256(0x123));
        bool[] memory flags = new bool[](3);
        bytes32[] memory branchLeaves = new bytes32[](1);
        branchLeaves[0] = bytes32(uint256(0x456));

        try target.multiProofMemory(proof, flags, branchLeaves) returns (
            bytes32
        ) {
            revert("expected invalid multiproof");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("MerkleProof: invalid multiproof")),
                "reason"
            );
        }
    }
}
