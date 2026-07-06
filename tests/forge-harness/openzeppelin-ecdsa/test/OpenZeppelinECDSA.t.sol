// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "../src/OpenZeppelinECDSA.sol";

contract OpenZeppelinECDSAForgeTest {
    function testRecoverVRSAndUsingFor() public {
        OpenZeppelinECDSAHarness harness = new OpenZeppelinECDSAHarness();
        uint256 privateKey = 0xA11CE;
        address signer = vmAddr(privateKey);
        bytes32 hash = keccak256("solid-core-spine ecdsa");
        (uint8 v, bytes32 r, bytes32 s) = vmSign(privateKey, hash);

        (address recovered, OpenZeppelinECDSA.RecoverError recoverError, bytes32 arg) =
            harness.tryRecoverVRS(hash, v, r, s);
        require(recovered == signer, "try recovered");
        require(recoverError == OpenZeppelinECDSA.RecoverError.NoError, "err");
        require(arg == bytes32(0), "arg");
        require(harness.recoverVRS(hash, v, r, s) == signer, "recover");
        require(harness.recoverUsingFor(hash, v, r, s) == signer, "using");
    }

    function testRecoverERC2098ShortSignature() public {
        OpenZeppelinECDSAHarness harness = new OpenZeppelinECDSAHarness();
        uint256 privateKey = 0xB0B;
        address signer = vmAddr(privateKey);
        bytes32 hash = keccak256("solid-core-spine short ecdsa");
        (uint8 v, bytes32 r, bytes32 s) = vmSign(privateKey, hash);
        bytes32 vs = bytes32(uint256(s) | (uint256(v - 27) << 255));

        (address recovered, OpenZeppelinECDSA.RecoverError recoverError, bytes32 arg) =
            harness.tryRecoverShort(hash, r, vs);
        require(recovered == signer, "short recovered");
        require(recoverError == OpenZeppelinECDSA.RecoverError.NoError, "err");
        require(arg == bytes32(0), "arg");
        require(harness.recoverShort(hash, r, vs) == signer, "recover short");
    }

    function testHighSReturnsErrorAndRecoverReverts() public {
        OpenZeppelinECDSAHarness harness = new OpenZeppelinECDSAHarness();
        bytes32 hash = keccak256("solid-core-spine high s");
        bytes32 highS = bytes32(uint256(harness.halfOrderLimit()) + 1);
        bytes32 r = bytes32(uint256(0x1234));

        (address recovered, OpenZeppelinECDSA.RecoverError recoverError, bytes32 arg) =
            harness.tryRecoverVRS(hash, 27, r, highS);
        require(recovered == address(0), "high s recovered");
        require(
            recoverError == OpenZeppelinECDSA.RecoverError.InvalidSignatureS,
            "high s err"
        );
        require(arg == highS, "high s arg");

        try harness.recoverVRS(hash, 27, r, highS) {
            revert("expected high s revert");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinECDSA.ECDSAInvalidSignatureS.selector,
                            highS
                        )
                    ),
                "high s revert data"
            );
        }
    }

    function testInvalidSignerReturnsErrorAndRecoverReverts() public {
        OpenZeppelinECDSAHarness harness = new OpenZeppelinECDSAHarness();
        bytes32 hash = keccak256("solid-core-spine bad signer");
        bytes32 r = bytes32(uint256(0x1234));
        bytes32 s = bytes32(uint256(0x5678));

        (address recovered, OpenZeppelinECDSA.RecoverError recoverError, bytes32 arg) =
            harness.tryRecoverVRS(hash, 29, r, s);
        require(recovered == address(0), "bad recovered");
        require(
            recoverError == OpenZeppelinECDSA.RecoverError.InvalidSignature,
            "bad err"
        );
        require(arg == bytes32(0), "bad arg");

        try harness.recoverVRS(hash, 29, r, s) {
            revert("expected invalid signature revert");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinECDSA.ECDSAInvalidSignature.selector
                        )
                    ),
                "bad revert data"
            );
        }
    }

    function vmSign(uint256 privateKey, bytes32 digest)
        private
        returns (uint8 v, bytes32 r, bytes32 s)
    {
        Vm vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
        return vm.sign(privateKey, digest);
    }

    function vmAddr(uint256 privateKey) private returns (address) {
        Vm vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
        return vm.addr(privateKey);
    }
}

interface Vm {
    function sign(uint256 privateKey, bytes32 digest)
        external
        returns (uint8 v, bytes32 r, bytes32 s);

    function addr(uint256 privateKey) external returns (address);
}
