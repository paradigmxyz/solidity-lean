// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface StorageRefundVm {
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
    function store(address target, bytes32 slot, bytes32 value) external;
    function load(address target, bytes32 slot) external view returns (bytes32 value);
    function coolSlot(address target, bytes32 slot) external;
}

contract StorageRefundParityTest {
    StorageRefundVm internal constant vm = StorageRefundVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant ORIGINAL_TARGET = 0x1000000000000000000000000000000000000011;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function setUp() public {
        vm.deal(ORIGINAL_TARGET, 0);
        vm.store(ORIGINAL_TARGET, bytes32(0), bytes32(uint256(5)));
        vm.coolSlot(ORIGINAL_TARGET, bytes32(0));
    }

    function testDirtyCurrentClearThenRecreateRefundParity() public {
        bytes memory code = hex"5f5f5560075f5500";
        runDirtyStorageRefundCase("dirty-current-clear-then-recreate-refund", code, 5);
    }

    function testDirtyCurrentClearThenRestoreRefundParity() public {
        bytes memory code = hex"5f5f5560055f5500";
        runDirtyStorageRefundCase("dirty-current-clear-then-restore-refund", code, 5);
    }

    function testDirtyCurrentChangeThenRestoreRefundParity() public {
        bytes memory code = hex"60075f5560055f5500";
        runDirtyStorageRefundCase("dirty-current-change-then-restore-refund", code, 5);
    }

    function testOriginalNonzeroClearThenRecreateRefundDebitParity() public {
        bytes memory code = hex"5f5f5560075f5500";
        runPresetStorageRefundCase("original-nonzero-clear-then-recreate-refund-debit", code, 5);
    }

    function testOriginalNonzeroClearThenRestoreRefundParity() public {
        bytes memory code = hex"5f5f5560055f5500";
        runPresetStorageRefundCase("original-nonzero-clear-then-restore-refund", code, 5);
    }

    function testOriginalNonzeroDirtyResetOriginalRefundParity() public {
        bytes memory code = hex"60075f5560055f5500";
        runPresetStorageRefundCase("original-nonzero-dirty-reset-original-refund", code, 5);
    }

    function testSstoreSetClearThenSetRefundParity() public {
        bytes memory code = hex"60075f555f5f5560095f5500";
        runDirtyStorageRefundCase("sstore-set-clear-then-set-refund", code, 0);
    }

    function testSloadWarmsSlotBeforeSstoreParity() public {
        bytes memory code = hex"5f5460075f5500";
        runDirtyStorageRefundCase("sload-warms-slot-before-sstore", code, 0);
    }

    function testRepeatedSstoreUsesWarmDirtySlotParity() public {
        bytes memory code = hex"60075f5560085f5500";
        runDirtyStorageRefundCase("repeated-sstore-uses-warm-dirty-slot", code, 0);
    }

    function runDirtyStorageRefundCase(string memory name, bytes memory code, uint256 currentValue) internal {
        address target = installRuntime(TARGET, code);
        bytes32 slot = bytes32(0);
        bytes32 current = bytes32(currentValue);

        vm.deal(target, 0);
        vm.store(target, slot, current);

        runStorageRefundCase(name, target, code, current, bytes32(0));
    }

    function runPresetStorageRefundCase(string memory name, bytes memory code, uint256 originalValue) internal {
        address target = installRuntime(ORIGINAL_TARGET, code);
        bytes32 current = bytes32(originalValue);

        runStorageRefundCase(name, target, code, current, current);
    }

    function runStorageRefundCase(
        string memory name,
        address target,
        bytes memory code,
        bytes32 current,
        bytes32 original
    ) internal {
        bytes32 slot = bytes32(0);
        vm.coolSlot(target, slot);

        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        StorageRefundVm.Gas memory gas = vm.lastCallGas();
        bytes32 finalValue = vm.load(target, slot);

        string[] memory command = new string[](51);
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
        command[30] = uintToString(target.balance);
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
        command[43] = "--address";
        command[44] = addressArg(target);
        command[45] = "--storage";
        command[46] = string.concat(wordHex(slot), "=", wordHex(current));
        command[47] = "--original-storage";
        command[48] = string.concat(wordHex(slot), "=", wordHex(original));
        command[49] = "--expect-storage";
        command[50] = string.concat(wordHex(slot), "=", wordHex(finalValue));

        vm.ffi(command);
    }

    function installRuntime(address target, bytes memory code) internal returns (address) {
        vm.etch(target, code);
        require(target.code.length == code.length, "runtime not installed");
        return target;
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
