// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface PrecompileValueVm {
    struct Gas {
        uint64 gasLimit;
        uint64 gasTotalUsed;
        uint64 gasMemoryUsed;
        int64 gasRefunded;
        uint64 gasRemaining;
    }

    function ffi(string[] calldata command) external returns (bytes memory result);
    function lastCallGas() external view returns (Gas memory gas);
    function etch(address target, bytes calldata newRuntimeBytecode) external;
    function deal(address target, uint256 newBalance) external;
}

contract PrecompileValueRollbackSubject {
    function ecaddWithValue(bytes calldata input, uint256 amount)
        external
        payable
        returns (bool ok, bytes memory output, uint256 precompileBalance, uint256 selfBalance)
    {
        (ok, output) = address(6).call{value: amount}(input);
        return (ok, output, address(6).balance, address(this).balance);
    }
}

contract PrecompileValueRollbackParityTest {
    PrecompileValueVm internal constant vm = PrecompileValueVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testEcaddInvalidPointCallValueRollbackParity() public {
        bytes memory input =
            abi.encodePacked(bytes32(uint256(1)), bytes32(uint256(1)), bytes32(uint256(0)), bytes32(uint256(0)));
        bytes memory data = abi.encodeCall(PrecompileValueRollbackSubject.ecaddWithValue, (input, uint256(123)));
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);

        runBn254FailureCase(
            "ecadd-invalid-point-call-value-rollback",
            type(PrecompileValueRollbackSubject).runtimeCode,
            data,
            500,
            failures
        );
    }

    function testEcaddInvalidPointClearsReturndataKeepsOutputParity() public {
        bytes memory input =
            abi.encodePacked(bytes32(uint256(1)), bytes32(uint256(1)), bytes32(uint256(0)), bytes32(uint256(0)));
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a05260015f5260016020525f6040525f606052602060a060805f5f6006620f4240f15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);

        runBn254FailureCase("ecadd-invalid-point-clears-returndata-keeps-output", code, hex"", 0, failures);
    }

    function testEcaddInvalidPointClearsReturndataBeforeReturndataCopyOobParity() public {
        bytes memory input =
            abi.encodePacked(bytes32(uint256(1)), bytes32(uint256(1)), bytes32(uint256(0)), bytes32(uint256(0)));
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f15060015f5260016020525f6040525f6060525f5f60805f5f6006620f4240f150600160005f3e00";
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);

        runBn254FailureCaseSkippingGas(
            "ecadd-invalid-point-clears-returndata-returndatacopy-oob", code, hex"", 0, failures
        );
    }

    function testEcmulInvalidPointClearsReturndataKeepsOutputParity() public {
        bytes memory input = abi.encodePacked(bytes32(uint256(1)), bytes32(uint256(1)), bytes32(uint256(1)));
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060605f5f6007620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);

        runBn254FailureCaseWithFailures(
            "ecmul-invalid-point-clears-returndata-keeps-output",
            code,
            input,
            0,
            address(7),
            new string[](0),
            failures,
            new string[](0)
        );
    }

    function testEcpairingInvalidPointClearsReturndataKeepsOutputParity() public {
        bytes memory input = abi.encodePacked(
            bytes32(uint256(1)),
            bytes32(uint256(1)),
            bytes32(uint256(0)),
            bytes32(uint256(0)),
            bytes32(uint256(0)),
            bytes32(uint256(0))
        );
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060c05f5f6008620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);

        runBn254FailureCaseWithFailures(
            "ecpairing-invalid-point-clears-returndata-keeps-output",
            code,
            input,
            0,
            address(8),
            new string[](0),
            new string[](0),
            failures
        );
    }

    function testEcpairingInvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f6008620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "ecpairing-invalid-length-clears-returndata-keeps-output-no-oracle", code, hex"00", 0, address(8), failures
        );
    }

    function testEcaddPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a052604060a05f5f5f60066095f15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "ecadd-precompile-oog-clears-returndata-keeps-output-no-oracle", code, hex"", 0, address(6), failures
        );
    }

    function testEcmulPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a052604060a05f5f5f600761176ff15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "ecmul-precompile-oog-clears-returndata-keeps-output-no-oracle", code, hex"", 0, address(7), failures
        );
    }

    function testEcpairingPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a052602060a05f5f5f600861afc7f15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "ecpairing-precompile-oog-clears-returndata-keeps-output-no-oracle", code, hex"", 0, address(8), failures
        );
    }

    function testIdentityPrecompileOogClearsReturndataKeepsOutputParity() public {
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a052602060a060205f5f60046011f15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "identity-precompile-oog-clears-returndata-keeps-output", code, hex"", 0, address(4), failures
        );
    }

    function testIdentityPrecompileCallValueOogRollsBackKeepsOutputParity() public {
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a052602060a06160005f60076004600ef15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "identity-precompile-call-value-oog-rollback-keeps-output", code, hex"", 500, address(4), failures
        );
    }

    function testEcrecoverInvalidSignatureClearsReturndataKeepsOutputParity() public {
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a052602060a060805f5f6001620f4240f15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "ecrecover-invalid-signature-clears-returndata-keeps-output", code, hex"", 0, address(1), failures
        );
    }

    function testEcrecoverPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a052602060a060805f5f6001610bb7f15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "ecrecover-precompile-oog-clears-returndata-keeps-output-no-oracle", code, hex"", 0, address(1), failures
        );
    }

    function testSha256PrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a052602060a060205f5f6002603bf15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "sha256-precompile-oog-clears-returndata-keeps-output-no-oracle", code, hex"", 0, address(2), failures
        );
    }

    function testRipemd160PrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"602a5f526020608060205f5f6004620f4240f150609960a052602060a060205f5f60036102cff15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "ripemd160-precompile-oog-clears-returndata-keeps-output-no-oracle", code, hex"", 0, address(3), failures
        );
    }

    function testP256InvalidSignatureClearsReturndataKeepsOutputParity() public {
        bytes memory input = p256InvalidSignatureInput();
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609960a052602060a060a05f5f610100620f4240f15f523d60205260a05160405260605ff3";
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);

        runP256FailureCase(
            "p256-invalid-signature-clears-returndata-keeps-output", code, input, 0, address(0x100), failures
        );
    }

    function testP256InvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f610100620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "p256-invalid-length-clears-returndata-keeps-output-no-oracle", code, hex"00", 0, address(0x100), failures
        );
    }

    function testPointEvaluationInvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f600a620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "point-evaluation-invalid-length-clears-returndata-keeps-output-no-oracle",
            code,
            hex"00",
            0,
            address(0x0a),
            failures
        );
    }

    function testPointEvaluationInvalidProofClearsReturndataKeepsOutputParity() public {
        bytes memory input = new bytes(192);
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060c05f5f600a620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);

        runPointEvaluationFailureCase(
            "point-evaluation-invalid-proof-clears-returndata-keeps-output", code, input, 0, address(0x0a), failures
        );
    }

    function testPointEvaluationPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory input = new bytes(192);
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060c05f5f600a61c34ff15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "point-evaluation-precompile-oog-clears-returndata-keeps-output-no-oracle",
            code,
            input,
            0,
            address(0x0a),
            failures
        );
    }

    function testP256PrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory input = p256ValidInput();
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060a05f5f610100611af3f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "p256-precompile-oog-clears-returndata-keeps-output-no-oracle", code, input, 0, address(0x100), failures
        );
    }

    function testBlake2fInvalidFinalFlagClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory input = blake2fInput(bytes1(0x02));
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060d55f5f6009620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "blake2f-invalid-final-flag-clears-returndata-keeps-output-no-oracle", code, input, 0, address(9), failures
        );
    }

    function testBlake2fInvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory input = hex"0000000c";
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060045f5f6009620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "blake2f-invalid-length-clears-returndata-keeps-output-no-oracle", code, input, 0, address(9), failures
        );
    }

    function testBlake2fPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory input = blake2fInput(bytes1(0x01));
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060d55f5f6009600bf15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "blake2f-precompile-oog-clears-returndata-keeps-output-no-oracle", code, input, 0, address(9), failures
        );
    }

    function testModexpPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory input = modexpInput();
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060635f5f60056101f3f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "modexp-precompile-oog-clears-returndata-keeps-output-no-oracle", code, input, 0, address(5), failures
        );
    }

    function testModexpZeroModulusClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory input = modexpZeroModulusInput();
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060605f5f6005620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "modexp-zero-modulus-clears-returndata-keeps-output-no-oracle", code, input, 0, address(5), failures
        );
    }

    function testBlsG1AddInvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f600b620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g1add-invalid-length-clears-returndata-keeps-output-no-oracle",
            code,
            hex"00",
            0,
            address(0x0b),
            failures
        );
    }

    function testBlsG2AddInvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f600d620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g2add-invalid-length-clears-returndata-keeps-output-no-oracle",
            code,
            hex"00",
            0,
            address(0x0d),
            failures
        );
    }

    function testBlsG1MsmInvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f600c620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g1msm-invalid-length-clears-returndata-keeps-output-no-oracle",
            code,
            hex"00",
            0,
            address(0x0c),
            failures
        );
    }

    function testBlsG1MsmEmptyInputClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f160996101005260206101005f5f5f600c620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g1msm-empty-input-clears-returndata-keeps-output-no-oracle", code, hex"", 0, address(0x0c), failures
        );
    }

    function testBlsG2MsmInvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f600e620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g2msm-invalid-length-clears-returndata-keeps-output-no-oracle",
            code,
            hex"00",
            0,
            address(0x0e),
            failures
        );
    }

    function testBlsG2MsmEmptyInputClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f160996101005260206101005f5f5f600e620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g2msm-empty-input-clears-returndata-keeps-output-no-oracle", code, hex"", 0, address(0x0e), failures
        );
    }

    function testBlsPairingInvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f600f620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-pairing-invalid-length-clears-returndata-keeps-output-no-oracle",
            code,
            hex"00",
            0,
            address(0x0f),
            failures
        );
    }

    function testBlsPairingEmptyInputClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f160996101005260206101005f5f5f600f620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-pairing-empty-input-clears-returndata-keeps-output-no-oracle", code, hex"", 0, address(0x0f), failures
        );
    }

    function testBlsMapFpToG1InvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f6010620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-map-fp-to-g1-invalid-length-clears-returndata-keeps-output-no-oracle",
            code,
            hex"00",
            0,
            address(0x10),
            failures
        );
    }

    function testBlsMapFp2ToG2InvalidLengthClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060015f5f6011620f4240f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-map-fp2-to-g2-invalid-length-clears-returndata-keeps-output-no-oracle",
            code,
            hex"00",
            0,
            address(0x11),
            failures
        );
    }

    function testBlsG2AddPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f160996101005260206101006102005f5f600d610257f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g2add-precompile-oog-clears-returndata-keeps-output-no-oracle",
            code,
            new bytes(512),
            0,
            address(0x0d),
            failures
        );
    }

    function testBlsG1AddPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f160996101005260206101006101005f5f600b610176f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g1add-precompile-oog-clears-returndata-keeps-output-no-oracle",
            code,
            new bytes(256),
            0,
            address(0x0b),
            failures
        );
    }

    function testBlsG1MsmPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060a05f5f600c612edff15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g1msm-precompile-oog-clears-returndata-keeps-output-no-oracle",
            code,
            new bytes(160),
            0,
            address(0x0c),
            failures
        );
    }

    function testBlsMapFpToG1PrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060405f5f601061157bf15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-map-fp-to-g1-precompile-oog-clears-returndata-keeps-output-no-oracle",
            code,
            new bytes(64),
            0,
            address(0x10),
            failures
        );
    }

    function testBlsMapFp2ToG2PrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f1609961010052602061010060805f5f6011615cf7f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-map-fp2-to-g2-precompile-oog-clears-returndata-keeps-output-no-oracle",
            code,
            new bytes(128),
            0,
            address(0x11),
            failures
        );
    }

    function testBlsG2MsmPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f160996101005260206101006101205f5f600e6157e3f15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-g2msm-precompile-oog-clears-returndata-keeps-output-no-oracle",
            code,
            new bytes(288),
            0,
            address(0x0e),
            failures
        );
    }

    function testBlsPairingPrecompileOogClearsReturndataKeepsOutputNoOracleParity() public {
        bytes memory code =
            hex"365f5f37602a61020052602061018060206102005f6004620f4240f160996101005260206101006101805f5f600f6201129bf15f523d6020526101005160405260605ff3";
        string[] memory failures = new string[](0);

        runPrecompileCase(
            "bls-pairing-precompile-oog-clears-returndata-keeps-output-no-oracle",
            code,
            new bytes(384),
            0,
            address(0x0f),
            failures
        );
    }

    function runBn254FailureCase(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        string[] memory ecaddFailures
    ) internal {
        runBn254FailureCaseWithFailures(
            name, code, data, initialBalance, address(6), ecaddFailures, new string[](0), new string[](0)
        );
    }

    function runBn254FailureCaseWithFailures(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        address checkedPrecompile,
        string[] memory ecaddFailures,
        string[] memory ecmulFailures,
        string[] memory ecpairingFailures
    ) internal {
        runPrecompileCaseWithGasPolicy(
            name,
            code,
            data,
            initialBalance,
            checkedPrecompile,
            ecaddFailures,
            ecmulFailures,
            ecpairingFailures,
            new string[](0),
            new string[](0),
            false
        );
    }

    function runBn254FailureCaseSkippingGas(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        string[] memory ecaddFailures
    ) internal {
        runPrecompileCaseWithGasPolicy(
            name,
            code,
            data,
            initialBalance,
            address(6),
            ecaddFailures,
            new string[](0),
            new string[](0),
            new string[](0),
            new string[](0),
            true
        );
    }

    function runP256FailureCase(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        address checkedPrecompile,
        string[] memory p256Failures
    ) internal {
        runPrecompileCaseWithGasPolicy(
            name,
            code,
            data,
            initialBalance,
            checkedPrecompile,
            new string[](0),
            new string[](0),
            new string[](0),
            new string[](0),
            p256Failures,
            false
        );
    }

    function runPointEvaluationFailureCase(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        address checkedPrecompile,
        string[] memory pointEvaluationFailures
    ) internal {
        runPrecompileCaseWithGasPolicy(
            name,
            code,
            data,
            initialBalance,
            checkedPrecompile,
            new string[](0),
            new string[](0),
            new string[](0),
            pointEvaluationFailures,
            new string[](0),
            false
        );
    }

    function runPrecompileCase(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        address checkedPrecompile,
        string[] memory ecaddFailures
    ) internal {
        runPrecompileCaseWithGasPolicy(
            name,
            code,
            data,
            initialBalance,
            checkedPrecompile,
            ecaddFailures,
            new string[](0),
            new string[](0),
            new string[](0),
            new string[](0),
            false
        );
    }

    function runPrecompileCaseWithGasPolicy(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        address checkedPrecompile,
        string[] memory ecaddFailures,
        string[] memory ecmulFailures,
        string[] memory ecpairingFailures,
        string[] memory pointEvaluationFailures,
        string[] memory p256Failures,
        bool skipGas
    ) internal {
        vm.etch(TARGET, code);
        vm.deal(TARGET, initialBalance);
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(data);
        PrecompileValueVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](
            45 + (skipGas ? 1 : 0) + 2 * ecaddFailures.length + 2 * ecmulFailures.length + 2 * ecpairingFailures.length
                + 2 * pointEvaluationFailures.length + 2 * p256Failures.length
        );
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = hexString(data);
        command[9] = "--gas";
        command[10] = uintToString(gas.gasLimit);
        command[11] = "--success";
        command[12] = success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(output);
        command[15] = "--gas-used";
        command[16] = uintToString(gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(gas.gasRefunded);
        command[21] = "--caller";
        command[22] = addressArg(address(this));
        command[23] = "--origin";
        command[24] = addressArg(tx.origin);
        command[25] = "--callvalue";
        command[26] = "0";
        command[27] = "--balance";
        command[28] = uintToString(initialBalance);
        command[29] = "--expect-balance";
        command[30] = uintToString(TARGET.balance);
        command[31] = "--coinbase";
        command[32] = addressArg(block.coinbase);
        command[33] = "--timestamp";
        command[34] = uintToString(block.timestamp);
        command[35] = "--number";
        command[36] = uintToString(block.number);
        command[37] = "--block-gas-limit";
        command[38] = uintToString(block.gaslimit);
        command[39] = "--basefee";
        command[40] = uintToString(block.basefee);
        command[41] = "--chainid";
        command[42] = uintToString(block.chainid);

        uint256 cursor = 43;
        if (skipGas) {
            command[cursor++] = "--skip-gas";
        }
        for (uint256 i = 0; i < ecaddFailures.length; i++) {
            command[cursor++] = "--ecadd-fail";
            command[cursor++] = ecaddFailures[i];
        }
        for (uint256 i = 0; i < ecmulFailures.length; i++) {
            command[cursor++] = "--ecmul-fail";
            command[cursor++] = ecmulFailures[i];
        }
        for (uint256 i = 0; i < ecpairingFailures.length; i++) {
            command[cursor++] = "--ecpairing-fail";
            command[cursor++] = ecpairingFailures[i];
        }
        for (uint256 i = 0; i < pointEvaluationFailures.length; i++) {
            command[cursor++] = "--point-evaluation-fail";
            command[cursor++] = pointEvaluationFailures[i];
        }
        for (uint256 i = 0; i < p256Failures.length; i++) {
            command[cursor++] = "--p256-verify-fail";
            command[cursor++] = p256Failures[i];
        }
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(checkedPrecompile), "=0");

        vm.ffi(command);
    }

    function p256ValidInput() internal pure returns (bytes memory) {
        return abi.encodePacked(
            bytes32(0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023),
            bytes32(0x2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18),
            bytes32(0x4cd60b855d442f5b3c7b11eb6c4e0ae7525fe710fab9aa7c77a67f79e6fadd76),
            bytes32(0x2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838),
            bytes32(0xc7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e)
        );
    }

    function p256InvalidSignatureInput() internal pure returns (bytes memory) {
        bytes memory input = p256ValidInput();
        input[95] = bytes1(uint8(input[95]) ^ 0x01);
        return input;
    }

    function blake2fInput(bytes1 finalFlag) internal pure returns (bytes memory) {
        return abi.encodePacked(
            hex"0000000c",
            bytes32(0),
            bytes32(0),
            bytes32(0),
            bytes32(0),
            bytes32(0),
            bytes32(0),
            hex"0000000000000000",
            hex"0000000000000000",
            finalFlag
        );
    }

    function modexpInput() internal pure returns (bytes memory) {
        return abi.encodePacked(
            bytes32(uint256(1)), bytes32(uint256(1)), bytes32(uint256(1)), bytes1(0x02), bytes1(0x05), bytes1(0x0d)
        );
    }

    function modexpZeroModulusInput() internal pure returns (bytes memory) {
        return abi.encodePacked(bytes32(0), bytes32(0), bytes32(0));
    }

    function hexString(bytes memory data) internal pure returns (string memory) {
        bytes memory alphabet = "0123456789abcdef";
        bytes memory out = new bytes(2 + data.length * 2);
        out[0] = "0";
        out[1] = "x";
        for (uint256 i = 0; i < data.length; i++) {
            out[2 + i * 2] = alphabet[uint8(data[i]) >> 4];
            out[3 + i * 2] = alphabet[uint8(data[i]) & 0x0f];
        }
        return string(out);
    }

    function addressArg(address value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function uintToString(uint256 value) internal pure returns (string memory) {
        if (value == 0) return "0";
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }

    function intToString(int256 value) internal pure returns (string memory) {
        if (value >= 0) return uintToString(uint256(value));
        return string.concat("-", uintToString(uint256(-value)));
    }
}
