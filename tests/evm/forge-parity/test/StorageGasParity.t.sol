// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface StorageVm {
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
    function store(address target, bytes32 slot, bytes32 value) external;
    function load(address target, bytes32 slot) external view returns (bytes32 value);
    function coolSlot(address target, bytes32 slot) external;
}

contract StorageGasParityTest {
    StorageVm internal constant vm = StorageVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testSstoreLowGasGuardParity() public {
        bytes memory code = hex"60055f5500";
        address target = installRuntime(code);
        vm.store(target, bytes32(0), bytes32(uint256(5)));
        vm.coolSlot(target, bytes32(0));

        (bool success, bytes memory output) = target.call{gas: 2305}(hex"");
        StorageVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](50);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = "sstore-low-gas-guard";
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
        command[43] = "--skip-gas";
        command[44] = "--storage";
        command[45] = string.concat(wordHex(bytes32(0)), "=", wordHex(bytes32(uint256(5))));
        command[46] = "--original-storage";
        command[47] = string.concat(wordHex(bytes32(0)), "=", wordHex(bytes32(0)));
        command[48] = "--expect-storage";
        command[49] = string.concat(wordHex(bytes32(0)), "=", wordHex(vm.load(target, bytes32(0))));

        vm.ffi(command);
    }

    function testSstoreLowGasGuardBoundaryAllowsAt2301Parity() public {
        bytes memory code = hex"60055f5500";
        address target = installRuntime(code);
        bytes32 slot = bytes32(0);
        bytes32 current = bytes32(uint256(5));
        vm.store(target, slot, current);
        vm.coolSlot(target, slot);

        (bool success, bytes memory output) = target.call{gas: 2306}(hex"");
        StorageVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](49);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = "sstore-low-gas-guard-boundary-allows-at-2301";
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
        command[43] = "--storage";
        command[44] = string.concat(wordHex(slot), "=", wordHex(current));
        command[45] = "--original-storage";
        command[46] = string.concat(wordHex(slot), "=", wordHex(bytes32(0)));
        command[47] = "--expect-storage";
        command[48] = string.concat(wordHex(slot), "=", wordHex(vm.load(target, slot)));

        vm.ffi(command);
    }

    function testRootRevertRollsBackRefundBearingSstoreParity() public {
        bytes memory code = hex"5f5f555f5ffd";
        address target = installRuntime(code);
        bytes32 slot = bytes32(0);
        bytes32 current = bytes32(uint256(5));
        vm.store(target, slot, current);
        vm.coolSlot(target, slot);

        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        StorageVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](49);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = "root-revert-rolls-back-refund-bearing-sstore";
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
        command[43] = "--storage";
        command[44] = string.concat(wordHex(slot), "=", wordHex(current));
        command[45] = "--original-storage";
        command[46] = string.concat(wordHex(slot), "=", wordHex(bytes32(0)));
        command[47] = "--expect-storage";
        command[48] = string.concat(wordHex(slot), "=", wordHex(vm.load(target, slot)));

        vm.ffi(command);
    }

    function installRuntime(bytes memory code) internal returns (address target) {
        target = TARGET;
        vm.etch(target, code);
        require(target.code.length == code.length, "runtime not installed");
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
