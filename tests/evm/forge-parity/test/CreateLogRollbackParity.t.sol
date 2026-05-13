// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface CreateLogRollbackVm {
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
    function getNonce(address target) external view returns (uint64 nonce);
}

contract CreateLogRollbackParityTest {
    CreateLogRollbackVm internal constant vm =
        CreateLogRollbackVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    uint8 internal constant EXPECT_NO_LOGS = 0;
    uint8 internal constant EXPECT_CREATED_LOG = 1;
    uint8 internal constant EXPECT_TARGET_THEN_CREATED = 2;
    uint8 internal constant EXPECT_CREATED_THEN_TARGET = 3;

    struct LeanCheck {
        string name;
        bool useCreate2;
        bytes initCode;
        bytes32 initHash;
        bytes preimage;
        address expectedCreated;
        bytes code;
        uint64 rootNonce;
        bool success;
        bytes output;
        CreateLogRollbackVm.Gas gas;
        string[] expectedLogs;
        bool skipGas;
    }

    function testCreateConstructorLogCommitsParity() public {
        runCase("create-constructor-log-commits", false, successInitLog(), hex"", hex"00", EXPECT_CREATED_LOG, false);
    }

    function testCreateRevertRollsBackConstructorLogParity() public {
        runCase(
            "create-revert-rolls-back-constructor-log", false, revertInitLog(), hex"", hex"00", EXPECT_NO_LOGS, false
        );
    }

    function testCreateInvalidRollsBackConstructorLogParity() public {
        runCase(
            "create-invalid-rolls-back-constructor-log", false, invalidInitLog(), hex"", hex"00", EXPECT_NO_LOGS, false
        );
    }

    function testCreateMemoryOogRollsBackConstructorLogParity() public {
        runCase(
            "create-memory-oog-rolls-back-constructor-log",
            false,
            memoryOogInitLog(),
            hex"",
            hex"00",
            EXPECT_NO_LOGS,
            false
        );
    }

    function testParentRevertRollsBackCreateConstructorLogParity() public {
        runCase(
            "parent-revert-rolls-back-create-constructor-log",
            false,
            successInitLog(),
            hex"",
            hex"5f5ffd",
            EXPECT_NO_LOGS,
            false
        );
    }

    function testParentInvalidRollsBackCreateConstructorLogParity() public {
        runCase(
            "parent-invalid-rolls-back-create-constructor-log",
            false,
            successInitLog(),
            hex"",
            hex"fe",
            EXPECT_NO_LOGS,
            true
        );
    }

    function testParentMemoryOogRollsBackCreateConstructorLogParity() public {
        runCase(
            "parent-memory-oog-rolls-back-create-constructor-log",
            false,
            successInitLog(),
            hex"",
            hex"600162ffffff52",
            EXPECT_NO_LOGS,
            true
        );
    }

    function testCreateParentThenConstructorLogOrderParity() public {
        runCase(
            "create-parent-then-constructor-log-order",
            false,
            successInitLog(),
            log1Code(0x2b),
            hex"00",
            EXPECT_TARGET_THEN_CREATED,
            false
        );
    }

    function testCreateConstructorThenParentLogOrderParity() public {
        runCase(
            "create-constructor-then-parent-log-order",
            false,
            successInitLog(),
            hex"",
            abi.encodePacked(log1Code(0x2b), hex"00"),
            EXPECT_CREATED_THEN_TARGET,
            false
        );
    }

    function testCreate2ConstructorLogCommitsParity() public {
        runCase("create2-constructor-log-commits", true, successInitLog(), hex"", hex"00", EXPECT_CREATED_LOG, false);
    }

    function testCreate2RevertRollsBackConstructorLogParity() public {
        runCase(
            "create2-revert-rolls-back-constructor-log", true, revertInitLog(), hex"", hex"00", EXPECT_NO_LOGS, false
        );
    }

    function testParentRevertRollsBackCreate2ConstructorLogParity() public {
        runCase(
            "parent-revert-rolls-back-create2-constructor-log",
            true,
            successInitLog(),
            hex"",
            hex"5f5ffd",
            EXPECT_NO_LOGS,
            false
        );
    }

    function testCreate2ConstructorThenParentLogOrderParity() public {
        runCase(
            "create2-constructor-then-parent-log-order",
            true,
            successInitLog(),
            hex"",
            abi.encodePacked(log1Code(0x2b), hex"00"),
            EXPECT_CREATED_THEN_TARGET,
            false
        );
    }

    function runCase(
        string memory name,
        bool useCreate2,
        bytes memory initCode,
        bytes memory beforeCreate,
        bytes memory afterCreate,
        uint8 logExpectation,
        bool skipGas
    ) internal {
        LeanCheck memory check;
        check.name = name;
        check.useCreate2 = useCreate2;
        check.initCode = initCode;
        check.initHash = keccak256(initCode);
        check.rootNonce = vm.getNonce(TARGET);
        check.preimage = useCreate2
            ? create2AddressPreimage(TARGET, bytes32(0), check.initHash)
            : createAddressPreimage(TARGET, check.rootNonce);
        check.expectedCreated = address(uint160(uint256(keccak256(check.preimage))));
        check.code = createRuntime(useCreate2, initCode, beforeCreate, afterCreate);
        check.skipGas = skipGas;

        vm.etch(TARGET, check.code);
        require(TARGET.code.length == check.code.length, "runtime not installed");

        (check.success, check.output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        check.gas = vm.lastCallGas();
        check.expectedLogs = expectedLogSpecs(logExpectation, check.expectedCreated);

        runLeanCheck(check);
    }

    function runLeanCheck(LeanCheck memory check) internal {
        uint256 keccakCount = check.useCreate2 ? 2 : 1;
        string[] memory command =
            new string[](53 + (check.skipGas ? 1 : 0) + 2 * keccakCount + 2 * check.expectedLogs.length);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = check.name;
        command[5] = "--code";
        command[6] = hexString(check.code);
        command[7] = "--calldata";
        command[8] = "0x";
        command[9] = "--gas";
        command[10] = uintToString(check.gas.gasLimit);
        command[11] = "--success";
        command[12] = check.success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(check.output);
        command[15] = "--gas-used";
        command[16] = uintToString(check.gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(check.gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(check.gas.gasRefunded);
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
        command[44] = uintToString(check.rootNonce);
        command[45] = "--expect-nonce";
        command[46] = uintToString(vm.getNonce(TARGET));

        uint256 cursor = 47;
        if (check.useCreate2) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakArg(check.initCode, check.initHash);
        }
        command[cursor++] = "--keccak";
        command[cursor++] = keccakArg(check.preimage, keccak256(check.preimage));
        command[cursor++] = "--expect-account-balance";
        command[cursor++] =
            string.concat(addressArg(check.expectedCreated), "=", uintToString(check.expectedCreated.balance));
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] =
            string.concat(addressArg(check.expectedCreated), "=", uintToString(vm.getNonce(check.expectedCreated)));
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(check.expectedCreated), "=0x");
        if (check.skipGas) {
            command[cursor++] = "--skip-gas";
        }
        for (uint256 i = 0; i < check.expectedLogs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = check.expectedLogs[i];
        }

        vm.ffi(command);
    }

    function createRuntime(bool useCreate2, bytes memory initCode, bytes memory beforeCreate, bytes memory afterCreate)
        internal
        pure
        returns (bytes memory)
    {
        require(initCode.length < 256, "init too large");
        uint256 fixedLength = useCreate2 ? 12 : 11;
        uint256 initOffset = beforeCreate.length + fixedLength + afterCreate.length;
        require(initOffset < 256, "offset too large");
        if (useCreate2) {
            return abi.encodePacked(
                beforeCreate,
                bytes1(0x60),
                bytes1(uint8(initCode.length)),
                bytes1(0x60),
                bytes1(uint8(initOffset)),
                hex"5f39",
                bytes1(0x5f),
                bytes1(0x60),
                bytes1(uint8(initCode.length)),
                hex"5f5ff5",
                afterCreate,
                initCode
            );
        }
        return abi.encodePacked(
            beforeCreate,
            bytes1(0x60),
            bytes1(uint8(initCode.length)),
            bytes1(0x60),
            bytes1(uint8(initOffset)),
            hex"5f39",
            bytes1(0x60),
            bytes1(uint8(initCode.length)),
            hex"5f5ff0",
            afterCreate,
            initCode
        );
    }

    function expectedLogSpecs(uint8 expectation, address created) internal pure returns (string[] memory logs) {
        if (expectation == EXPECT_CREATED_LOG) {
            logs = new string[](1);
            logs[0] = log1Spec(created, 0x2a);
        } else if (expectation == EXPECT_TARGET_THEN_CREATED) {
            logs = new string[](2);
            logs[0] = log1Spec(TARGET, 0x2b);
            logs[1] = log1Spec(created, 0x2a);
        } else if (expectation == EXPECT_CREATED_THEN_TARGET) {
            logs = new string[](2);
            logs[0] = log1Spec(created, 0x2a);
            logs[1] = log1Spec(TARGET, 0x2b);
        } else {
            logs = new string[](0);
        }
    }

    function successInitLog() internal pure returns (bytes memory) {
        return abi.encodePacked(log1Code(0x2a), hex"5f5ff3");
    }

    function revertInitLog() internal pure returns (bytes memory) {
        return abi.encodePacked(log1Code(0x2a), hex"5f5ffd");
    }

    function invalidInitLog() internal pure returns (bytes memory) {
        return abi.encodePacked(log1Code(0x2a), hex"fe");
    }

    function memoryOogInitLog() internal pure returns (bytes memory) {
        return abi.encodePacked(log1Code(0x2a), hex"600162ffffff52");
    }

    function log1Code(uint256 topic) internal pure returns (bytes memory) {
        require(topic < 256, "topic too large");
        return abi.encodePacked(bytes1(0x60), bytes1(uint8(topic)), hex"5f5fa1");
    }

    function log1Spec(address emitter, uint256 topic) internal pure returns (string memory) {
        return string.concat(addressWordHex(emitter), "|", wordHex(bytes32(topic)), "|0x");
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

    function addressArg(address value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function addressWordHex(address value) internal pure returns (string memory) {
        return wordHex(bytes32(uint256(uint160(value))));
    }

    function wordHex(bytes32 value) internal pure returns (string memory) {
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
