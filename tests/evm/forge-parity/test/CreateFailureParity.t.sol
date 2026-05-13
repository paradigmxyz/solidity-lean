// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface CreateFailureVm {
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
    function getNonce(address target) external view returns (uint64 nonce);
    function setNonce(address target, uint64 nonce) external;
    function cool(address target) external;
}

contract CreateFailureParityTest {
    CreateFailureVm internal constant vm = CreateFailureVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    uint256 internal constant GAS_LIMIT = 1_000_000;
    uint256 internal constant LARGE_CREATE_GAS_LIMIT = 8_000_000;

    function testCreateValueInsufficientBalanceDoesNotIncrementNonceParity() public {
        bytes memory code = hex"5f5f6001f05f523d60205260405ff3";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](0);
        runCreateFailureCase("create-value-insufficient-balance-no-nonce", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreate2ValueInsufficientBalanceDoesNotIncrementNonceParity() public {
        bytes memory code = hex"5f5f5f6001f55f523d60205260405ff3";
        bytes32 initHash = keccak256(hex"");
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](0);
        runCreateFailureCase(
            "create2-value-insufficient-balance-no-nonce", code, vm.getNonce(TARGET), expectedCreated, keccaks
        );
    }

    function testCreateStopInitcodeCreatesEmptyRuntimeAccountParity() public {
        bytes memory code = hex"600160155f3960015f5ff05f523d60205260405ff300";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateFailureCase("create-stop-initcode-empty-runtime-account", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreateValueSuccessCommitsBalanceParity() public {
        bytes memory code = hex"600160165f3960015f6002f05f523d60205260405ff300";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create-value-success-commits-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testCreateValueRevertRollsBackBalanceParity() public {
        bytes memory code = hex"600360165f3960035f6002f05f523d60205260405ff35f5ffd";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create-value-revert-rolls-back-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testCreateValueInvalidRollsBackBalanceParity() public {
        bytes memory code = hex"600160165f3960015f6002f05f523d60205260405ff3fe";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create-value-invalid-rolls-back-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testCreateValueMemoryOogRollsBackBalanceParity() public {
        bytes memory code = hex"600760165f3960075f6002f05f523d60205260405ff3600162ffffff52";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create-value-memory-oog-rolls-back-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testCreateValueCodeDepositOogRollsBackBalanceParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code =
            abi.encodePacked(hex"600560295f3960055f6002f05073", expectedCreated, hex"315f5260205ff36117705ff3");
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create-value-code-deposit-oog-rolls-back-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testCreate2ValueSuccessCommitsBalanceParity() public {
        bytes memory code = hex"600160175f395f60015f6002f55f523d60205260405ff300";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"00";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create2-value-success-commits-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testCreate2SuccessClearsReturndataParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"6001600a5f3960015ff300";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code =
            hex"602a5f525f5f60205f5f6004620f4240f150600b60285f395f600b5f5ff55f523d60205260405ff36001600a5f3960015ff300";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateFundedExactGasCase(
            "create2-success-clears-returndata", code, 0, rootNonce, expectedCreated, keccaks, hex"00"
        );
    }

    function testCreate2ValueRevertRollsBackBalanceParity() public {
        bytes memory code = hex"600360175f395f60035f6002f55f523d60205260405ff35f5ffd";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"5f5ffd";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create2-value-revert-rolls-back-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testCreate2ValueInvalidRollsBackBalanceParity() public {
        bytes memory code = hex"600160175f395f60015f6002f55f523d60205260405ff3fe";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"fe";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create2-value-invalid-rolls-back-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testCreate2ValueMemoryOogRollsBackBalanceParity() public {
        bytes memory code = hex"600760175f395f60075f6002f55f523d60205260405ff3600162ffffff52";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"600162ffffff52";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create2-value-memory-oog-rolls-back-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testCreate2ValueCodeDepositOogRollsBackBalanceParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"6117705ff3";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code =
            abi.encodePacked(hex"600560295f395f60055f6002f573", expectedCreated, hex"315f5260205ff36117705ff3");
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "create2-value-code-deposit-oog-rolls-back-balance", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testRootRevertRollsBackSuccessfulCreateParity() public {
        bytes memory code = hex"6001600e5f3960015f5ff05f5ffd00";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateExactGasCase("root-revert-rolls-back-successful-create", code, rootNonce, expectedCreated, keccaks);
    }

    function testRootInvalidRollsBackSuccessfulCreateParity() public {
        bytes memory code = hex"6001600c5f3960015f5ff0fe00";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateExactGasCaseSkippingGas(
            "root-invalid-rolls-back-successful-create", code, rootNonce, expectedCreated, keccaks
        );
    }

    function testRootMemoryOogRollsBackSuccessfulCreateParity() public {
        bytes memory code = hex"600160125f3960015f5ff0600162ffffff5200";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateExactGasCaseSkippingGas(
            "root-memory-oog-rolls-back-successful-create", code, rootNonce, expectedCreated, keccaks
        );
    }

    function testRootRevertRollsBackSuccessfulValueCreateParity() public {
        bytes memory code = hex"6001600f5f3960015f6002f05f5ffd00";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "root-revert-rolls-back-successful-value-create", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testRootRevertRollsBackSuccessfulValueCreate2Parity() public {
        bytes memory code = hex"600160105f395f60015f6002f55f5ffd00";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"00";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateFundedExactGasCase(
            "root-revert-rolls-back-successful-value-create2", code, 5, rootNonce, expectedCreated, keccaks, hex""
        );
    }

    function testRootInvalidRollsBackSuccessfulCreate2Parity() public {
        bytes memory code = hex"6001600d5f395f60015f5ff5fe00";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"00";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateExactGasCaseSkippingGas(
            "root-invalid-rolls-back-successful-create2", code, rootNonce, expectedCreated, keccaks
        );
    }

    function testRootMemoryOogRollsBackSuccessfulCreate2Parity() public {
        bytes memory code = hex"600160135f395f60015f5ff5600162ffffff5200";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"00";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateExactGasCaseSkippingGas(
            "root-memory-oog-rolls-back-successful-create2", code, rootNonce, expectedCreated, keccaks
        );
    }

    function testCreateZeroLengthHighOffsetNoExpansionParity() public {
        bytes memory code = hex"5f62ffffff5ff05f523d60205260405ff3";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateExactGasCase("create-zero-length-high-offset-no-expansion", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreateZeroLengthMaxOffsetNoExpansionParity() public {
        bytes memory code = abi.encodePacked(hex"5f7f", bytes32(type(uint256).max), hex"5ff05f523d60205260405ff3");
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCreateExactGasCase("create-zero-length-max-offset-no-expansion", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreate2ZeroLengthHighOffsetNoExpansionParity() public {
        bytes memory code = hex"5f5f62ffffff5ff55f523d60205260405ff3";
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateExactGasCase("create2-zero-length-high-offset-no-expansion", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreate2ZeroLengthMaxOffsetNoExpansionParity() public {
        bytes memory code = abi.encodePacked(hex"5f5f7f", bytes32(type(uint256).max), hex"5ff55f523d60205260405ff3");
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreateExactGasCase("create2-zero-length-max-offset-no-expansion", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreateInitcodeMemoryExpansionOogDoesNotIncrementNonceParity() public {
        bytes memory code = hex"602062ffffff5ff0";
        runCreateMemoryOogCase("create-initcode-memory-expansion-oog-no-nonce", code, vm.getNonce(TARGET));
    }

    function testCreate2InitcodeMemoryExpansionOogDoesNotIncrementNonceParity() public {
        bytes memory code = hex"5f602062ffffff5ff5";
        runCreateMemoryOogCase("create2-initcode-memory-expansion-oog-no-nonce", code, vm.getNonce(TARGET));
    }

    function testCreateOversizedInitcodeFailureIncrementsNonceParity() public {
        bytes memory code = hex"61c0015f5ff0";
        string[] memory keccaks = new string[](0);
        runCreateExactGasCase(
            "create-oversized-initcode-failure-increments-nonce",
            code,
            vm.getNonce(TARGET),
            address(uint160(0xc001)),
            keccaks
        );
    }

    function testCreate2OversizedInitcodeFailureIncrementsNonceParity() public {
        bytes memory code = hex"5f61c0015f5ff5";
        string[] memory keccaks = new string[](0);
        runCreateExactGasCase(
            "create2-oversized-initcode-failure-increments-nonce",
            code,
            vm.getNonce(TARGET),
            address(uint160(0xc002)),
            keccaks
        );
    }

    function testCreateRevertWarmsCreatedAddressParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code =
            abi.encodePacked(hex"67602a5f5260205ffd5f52600860185ff05073", expectedCreated, hex"315f5260205ff3");
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));

        runCreateExactGasCase("create-revert-warms-created-address", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreateCodeDepositOogWarmsCreatedAddressParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code =
            abi.encodePacked(hex"600560285f3960055f5ff05073", expectedCreated, hex"315f5260205ff36117705ff3");
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));

        runCreateExactGasCase(
            "create-code-deposit-oog-warms-created-address", code, rootNonce, expectedCreated, keccaks
        );
    }

    function testCreateCodeDepositOogClearsReturndataParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = hex"6005601a5f3960055f5ff05f523d6020523d5f60403e60605ff36117705ff3";
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));

        runCreateExactGasCase("create-code-deposit-oog-clears-returndata", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreateRuntimeCodeSizeLimitFailureParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = hex"6005601a5f3960055f5ff05f523d6020523d5f60403e60605ff36160015ff3";
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));

        runCreateExactGasCase("create-runtime-code-size-limit-failure", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreateRuntimeCodeSizeLimitBoundarySuccessParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = hex"600560155f3960055f5ff05f523d60205260405ff36160005ff3";
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));

        runCreateFundedExactGasCodeSizeCaseWithGasLimit(
            "create-runtime-code-size-limit-boundary-success",
            code,
            LARGE_CREATE_GAS_LIMIT,
            0,
            rootNonce,
            expectedCreated,
            keccaks,
            24576
        );
    }

    function testCreateValueCollisionRollsBackBalanceParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory collisionCode = hex"00";
        bytes memory code =
            abi.encodePacked(hex"600560285f39600260055ff073", expectedCreated, hex"315f5260205ff360006000f3");
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));

        runCreateFundedCollisionExactGasCase(
            "create-value-collision-rolls-back-balance", code, 5, rootNonce, expectedCreated, collisionCode, keccaks
        );
    }

    function testCreateCollisionClearsReturndataParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory collisionCode = hex"602a5f5260205ff3";
        bytes memory code = hex"602a5f525f5f60205f5f6004620f4240f15060015f5ff05f523d60205260405ff3";
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));

        runCreateCollisionExactGasCase(
            "create-collision-clears-returndata", code, rootNonce, expectedCreated, collisionCode, keccaks
        );
    }

    function testCreateNonceCollisionClearsReturndataParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = hex"602a5f525f5f60205f5f6004620f4240f15060015f5ff05f523d60205260405ff3";
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));

        runCreateNonceCollisionExactGasCase(
            "create-nonce-collision-clears-returndata", code, rootNonce, expectedCreated, keccaks
        );
    }

    function testCreate2RevertWarmsCreatedAddressParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"602a5f5260205ffd";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code =
            abi.encodePacked(hex"67602a5f5260205ffd5f525f600860185ff55073", expectedCreated, hex"315f5260205ff3");
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateExactGasCase("create2-revert-warms-created-address", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreate2RevertReturndataParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"602a5f5260205ffd";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = hex"600860175f395f60085f5ff55f523d5f60403e60605ff3602a5f5260205ffd";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateExactGasCase("create2-revert-returndata", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreate2CodeDepositOogClearsReturndataParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"6117705ff3";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = hex"6005601b5f395f60055f5ff55f523d6020523d5f60403e60605ff36117705ff3";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateExactGasCase("create2-code-deposit-oog-clears-returndata", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreate2RuntimeCodeSizeLimitFailureParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"6160015ff3";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = hex"6005601b5f395f60055f5ff55f523d6020523d5f60403e60605ff36160015ff3";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateExactGasCase("create2-runtime-code-size-limit-failure", code, rootNonce, expectedCreated, keccaks);
    }

    function testCreate2RuntimeCodeSizeLimitBoundarySuccessParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"6160005ff3";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = hex"600560165f395f60055f5ff55f523d60205260405ff36160005ff3";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateFundedExactGasCodeSizeCaseWithGasLimit(
            "create2-runtime-code-size-limit-boundary-success",
            code,
            LARGE_CREATE_GAS_LIMIT,
            0,
            rootNonce,
            expectedCreated,
            keccaks,
            24576
        );
    }

    function testCreate2ValueCollisionRollsBackBalanceParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"60006000f3";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory collisionCode = hex"00";
        bytes memory code =
            abi.encodePacked(hex"600560295f395f60055f6002f573", expectedCreated, hex"315f5260205ff360006000f3");
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateFundedCollisionExactGasCase(
            "create2-value-collision-rolls-back-balance", code, 5, rootNonce, expectedCreated, collisionCode, keccaks
        );
    }

    function testCreate2CollisionClearsReturndataParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"00";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory collisionCode = hex"602a5f5260205ff3";
        bytes memory code = hex"602a5f525f5f60205f5f6004620f4240f1505f60015f5ff55f523d60205260405ff3";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateCollisionExactGasCase(
            "create2-collision-clears-returndata", code, rootNonce, expectedCreated, collisionCode, keccaks
        );
    }

    function testCreate2NonceCollisionClearsReturndataParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"00";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = hex"602a5f525f5f60205f5f6004620f4240f1505f60015f5ff55f523d60205260405ff3";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateNonceCollisionExactGasCase(
            "create2-nonce-collision-clears-returndata", code, rootNonce, expectedCreated, keccaks
        );
    }

    function testCreate2CollisionWarmsCreatedAddressParity() public {
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"60006000f3";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory collisionCode = hex"00";
        bytes memory code =
            abi.encodePacked(hex"600560285f395f60055f5ff573", expectedCreated, hex"315f5260205ff360006000f3");
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));

        runCreateCollisionExactGasCase(
            "create2-collision-warms-created-address", code, rootNonce, expectedCreated, collisionCode, keccaks
        );
    }

    function runCreateFailureCase(
        string memory name,
        bytes memory code,
        uint64 rootNonce,
        address expectedCreated,
        string[] memory keccakAssignments
    ) internal {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        CreateFailureVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](54 + 2 * keccakAssignments.length);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
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
        command[28] = "0";
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
        command[43] = "--nonce";
        command[44] = uintToString(rootNonce);
        command[45] = "--expect-nonce";
        command[46] = uintToString(vm.getNonce(TARGET));

        uint256 cursor = 47;
        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreated.balance));
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(vm.getNonce(expectedCreated)));
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=0x");
        command[cursor++] = "--skip-gas";

        vm.ffi(command);
    }

    function runCreateExactGasCase(
        string memory name,
        bytes memory code,
        uint64 rootNonce,
        address expectedCreated,
        string[] memory keccakAssignments
    ) internal {
        runCreateExactGasCaseWithGasMode(name, code, rootNonce, expectedCreated, keccakAssignments, false);
    }

    function runCreateExactGasCaseSkippingGas(
        string memory name,
        bytes memory code,
        uint64 rootNonce,
        address expectedCreated,
        string[] memory keccakAssignments
    ) internal {
        runCreateExactGasCaseWithGasMode(name, code, rootNonce, expectedCreated, keccakAssignments, true);
    }

    function runCreateExactGasCaseWithGasMode(
        string memory name,
        bytes memory code,
        uint64 rootNonce,
        address expectedCreated,
        string[] memory keccakAssignments,
        bool skipGas
    ) internal {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        CreateFailureVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](53 + (skipGas ? 1 : 0) + 2 * keccakAssignments.length);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
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
        command[28] = "0";
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
        command[43] = "--nonce";
        command[44] = uintToString(rootNonce);
        command[45] = "--expect-nonce";
        command[46] = uintToString(vm.getNonce(TARGET));

        uint256 cursor = 47;
        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreated.balance));
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(vm.getNonce(expectedCreated)));
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=0x");
        if (skipGas) {
            command[cursor++] = "--skip-gas";
        }

        vm.ffi(command);
    }

    function runCreateFundedExactGasCase(
        string memory name,
        bytes memory code,
        uint256 initialBalance,
        uint64 rootNonce,
        address expectedCreated,
        string[] memory keccakAssignments,
        bytes memory expectedCreatedCode
    ) internal {
        runCreateFundedExactGasCaseWithGasLimit(
            name, code, GAS_LIMIT, initialBalance, rootNonce, expectedCreated, keccakAssignments, expectedCreatedCode
        );
    }

    function runCreateFundedExactGasCaseWithGasLimit(
        string memory name,
        bytes memory code,
        uint256 gasLimit,
        uint256 initialBalance,
        uint64 rootNonce,
        address expectedCreated,
        string[] memory keccakAssignments,
        bytes memory expectedCreatedCode
    ) internal {
        runCreateFundedExactGasCaseWithGasLimitAndExpectation(
            name,
            code,
            gasLimit,
            initialBalance,
            rootNonce,
            expectedCreated,
            keccakAssignments,
            expectedCreatedCode,
            false,
            0
        );
    }

    function runCreateFundedExactGasCodeSizeCaseWithGasLimit(
        string memory name,
        bytes memory code,
        uint256 gasLimit,
        uint256 initialBalance,
        uint64 rootNonce,
        address expectedCreated,
        string[] memory keccakAssignments,
        uint256 expectedCreatedCodeSize
    ) internal {
        runCreateFundedExactGasCaseWithGasLimitAndExpectation(
            name,
            code,
            gasLimit,
            initialBalance,
            rootNonce,
            expectedCreated,
            keccakAssignments,
            hex"",
            true,
            expectedCreatedCodeSize
        );
    }

    function runCreateFundedExactGasCaseWithGasLimitAndExpectation(
        string memory name,
        bytes memory code,
        uint256 gasLimit,
        uint256 initialBalance,
        uint64 rootNonce,
        address expectedCreated,
        string[] memory keccakAssignments,
        bytes memory expectedCreatedCode,
        bool expectCodeSize,
        uint256 expectedCreatedCodeSize
    ) internal {
        vm.etch(TARGET, code);
        vm.deal(TARGET, initialBalance);
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: gasLimit}(hex"");
        CreateFailureVm.Gas memory gas = vm.lastCallGas();
        if (expectCodeSize) {
            require(expectedCreated.code.length == expectedCreatedCodeSize, "unexpected created code size");
        }

        string[] memory command = new string[](53 + 2 * keccakAssignments.length);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
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
        command[43] = "--nonce";
        command[44] = uintToString(rootNonce);
        command[45] = "--expect-nonce";
        command[46] = uintToString(vm.getNonce(TARGET));

        uint256 cursor = 47;
        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreated.balance));
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(vm.getNonce(expectedCreated)));
        if (expectCodeSize) {
            command[cursor++] = "--expect-account-codesize";
            command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreatedCodeSize));
        } else {
            command[cursor++] = "--expect-account-code";
            command[cursor++] = string.concat(addressArg(expectedCreated), "=", hexString(expectedCreatedCode));
        }

        vm.ffi(command);
    }

    function runCreateMemoryOogCase(string memory name, bytes memory code, uint64 rootNonce) internal {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        CreateFailureVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](48);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
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
        command[28] = "0";
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
        command[43] = "--nonce";
        command[44] = uintToString(rootNonce);
        command[45] = "--expect-nonce";
        command[46] = uintToString(vm.getNonce(TARGET));
        command[47] = "--skip-gas";

        vm.ffi(command);
    }

    function runCreateCollisionExactGasCase(
        string memory name,
        bytes memory code,
        uint64 rootNonce,
        address expectedCreated,
        bytes memory collisionCode,
        string[] memory keccakAssignments
    ) internal {
        runCreateFundedCollisionExactGasCase(
            name, code, 0, rootNonce, expectedCreated, collisionCode, keccakAssignments
        );
    }

    function runCreateFundedCollisionExactGasCase(
        string memory name,
        bytes memory code,
        uint256 initialBalance,
        uint64 rootNonce,
        address expectedCreated,
        bytes memory collisionCode,
        string[] memory keccakAssignments
    ) internal {
        vm.etch(TARGET, code);
        vm.deal(TARGET, initialBalance);
        require(TARGET.code.length == code.length, "runtime not installed");
        vm.etch(expectedCreated, collisionCode);
        vm.cool(expectedCreated);

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        CreateFailureVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](55 + 2 * keccakAssignments.length);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
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
        command[43] = "--nonce";
        command[44] = uintToString(rootNonce);
        command[45] = "--expect-nonce";
        command[46] = uintToString(vm.getNonce(TARGET));

        uint256 cursor = 47;
        command[cursor++] = "--account";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", hexString(collisionCode));
        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreated.balance));
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(vm.getNonce(expectedCreated)));
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", hexString(collisionCode));

        vm.ffi(command);
    }

    function runCreateNonceCollisionExactGasCase(
        string memory name,
        bytes memory code,
        uint64 rootNonce,
        address expectedCreated,
        string[] memory keccakAssignments
    ) internal {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");
        vm.setNonce(expectedCreated, 1);
        vm.cool(expectedCreated);
        require(expectedCreated.code.length == 0, "collision code installed");
        require(vm.getNonce(expectedCreated) == 1, "collision nonce not set");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        CreateFailureVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](55 + 2 * keccakAssignments.length);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
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
        command[28] = "0";
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
        command[43] = "--nonce";
        command[44] = uintToString(rootNonce);
        command[45] = "--expect-nonce";
        command[46] = uintToString(vm.getNonce(TARGET));

        uint256 cursor = 47;
        command[cursor++] = "--account-nonce";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=1");
        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreated.balance));
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(vm.getNonce(expectedCreated)));
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=0x");

        vm.ffi(command);
    }

    function createAddressPreimage(address creator, uint256 nonce) internal pure returns (bytes memory) {
        bytes memory payload = abi.encodePacked(bytes1(0x94), creator, rlpSmallWord(nonce));
        return abi.encodePacked(bytes1(uint8(0xc0 + payload.length)), payload);
    }

    function create2AddressPreimage(address creator, bytes32 salt, bytes32 initHash)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(bytes1(0xff), creator, salt, initHash);
    }

    function rlpSmallWord(uint256 value) internal pure returns (bytes memory) {
        if (value == 0) return hex"80";
        require(value < 128, "nonce too large");
        return abi.encodePacked(bytes1(uint8(value)));
    }

    function keccakArg(bytes memory input, bytes32 output) internal pure returns (string memory) {
        return string.concat(hexString(input), "=", wordHex(output));
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

    function wordHex(bytes32 value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function addressArg(address value) internal pure returns (string memory) {
        return wordHex(bytes32(uint256(uint160(value))));
    }

    function uintToString(uint256 value) internal pure returns (string memory) {
        if (value == 0) {
            return "0";
        }
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
        if (value >= 0) {
            return uintToString(uint256(value));
        }
        return string.concat("-", uintToString(uint256(-value)));
    }
}
