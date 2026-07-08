// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/HashPrecompiles.sol";

// Ground-truth pinning for the sha256 (0x02) and ripemd160 (0x03) precompile
// builtins. Every expected constant is the value the real pinned-solc / Foundry
// EVM produced (read from the precompile return in a -vvvv trace); the Lean lane
// asserts the interpreter reproduces these same digests.
contract HashPrecompilesForgeTest {
    bytes constant WORD32 =
        hex"6162636465666768696a6b6c6d6e6f707172737475767778797a303132333435";
    bytes constant LONG40 =
        hex"6162636465666768696a6b6c6d6e6f707172737475767778797a3031323334353637383930313233";

    function testSha256() public {
        HashPrecompilesHarnessTarget t = new HashPrecompilesHarnessTarget();

        require(
            t.sha256Of("") ==
                0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855,
            "sha256 empty"
        );
        require(
            t.sha256Of(hex"010203") ==
                0x039058c6f2c0cb492c533b0a4d14ef77cc0f78abccced5287d84a1a2011cfb81,
            "sha256 short"
        );
        require(
            t.sha256Of(WORD32) ==
                0x653bb1245e828fcda4fa53fcd5a3def5bd7654e651f54b4132b73d74e64435c4,
            "sha256 word32"
        );
        require(
            t.sha256Of(LONG40) ==
                0x2fa2c189076e20488be2d1da4af97695cff36f38a0b528347b600f3e3912b353,
            "sha256 long40"
        );
    }

    function testRipemd160() public {
        HashPrecompilesHarnessTarget t = new HashPrecompilesHarnessTarget();

        require(
            t.ripemd160Word("") ==
                890993315260586290631548281360202943075753233713,
            "ripemd empty"
        );
        require(
            t.ripemd160Word(hex"010203") ==
                696340930168522892998195131872680409321950903639,
            "ripemd short"
        );
        require(
            t.ripemd160Word(WORD32) ==
                731965298338221626821500645460329338686522572377,
            "ripemd word32"
        );
        require(
            t.ripemd160Word(LONG40) ==
                1371049488833874687166849491603102752985797809355,
            "ripemd long40"
        );

        // bytes20 is left-aligned in a 32-byte word on the EVM: the 20-byte
        // digest occupies the high bytes, and bytes32(bytes20) right-pads with
        // zeros. Pin both the bytes20 identity and its left-aligned widening.
        require(
            t.ripemd160Of(hex"010203") ==
                bytes20(hex"79f901da2609f020adadbf2e5f68a16c8c3f7d57"),
            "ripemd bytes20"
        );
        require(
            bytes32(t.ripemd160Of(hex"010203")) ==
                0x79f901da2609f020adadbf2e5f68a16c8c3f7d57000000000000000000000000,
            "ripemd bytes20 left-aligned"
        );
    }
}
