// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface AccessWarmthVm {
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

contract AccessWarmthParityTest {
    AccessWarmthVm internal constant vm = AccessWarmthVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    address internal constant DESTRUCTEE = 0x3000000000000000000000000000000000000003;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testInitialContextAddressesAreWarmParity() public {
        bytes memory code = hex"30315033315032315041315f5260205ff3";
        runAccessWarmthCase("initial-context-addresses-are-warm", code, hex"00");
    }

    function testSuccessfulChildAccountAccessWarmsParentFrameParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"734000000000000000000000000000000000000004315000";
        runAccessWarmthCase("successful-child-account-access-warms-parent-frame", code, accountCode);
    }

    function testRevertedChildAccountAccessRollsBackWarmthParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"73400000000000000000000000000000000000000431505f5ffd";
        runAccessWarmthCase("reverted-child-account-access-rolls-back-warmth", code, accountCode);
    }

    function testSuccessfulChildExtcodesizeAccessWarmsParentFrameParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"7340000000000000000000000000000000000000043b5000";
        runAccessWarmthCase("successful-child-extcodesize-access-warms-parent-frame", code, accountCode);
    }

    function testRevertedChildExtcodesizeAccessRollsBackWarmthParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"7340000000000000000000000000000000000000043b505f5ffd";
        runAccessWarmthCase("reverted-child-extcodesize-access-rolls-back-warmth", code, accountCode);
    }

    function testSuccessfulChildExtcodehashAccessWarmsParentFrameParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"7340000000000000000000000000000000000000043f5000";
        runAccessWarmthCase("successful-child-extcodehash-access-warms-parent-frame", code, accountCode);
    }

    function testRevertedChildExtcodehashAccessRollsBackWarmthParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"7340000000000000000000000000000000000000043f505f5ffd";
        runAccessWarmthCase("reverted-child-extcodehash-access-rolls-back-warmth", code, accountCode);
    }

    function testSuccessfulChildZeroLengthExtcodecopyAccessWarmsParentFrameParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"5f5f5f7340000000000000000000000000000000000000043c00";
        runAccessWarmthCase("successful-child-zero-length-extcodecopy-access-warms-parent-frame", code, accountCode);
    }

    function testRevertedChildZeroLengthExtcodecopyAccessRollsBackWarmthParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"5f5f5f7340000000000000000000000000000000000000043c5f5ffd";
        runAccessWarmthCase("reverted-child-zero-length-extcodecopy-access-rolls-back-warmth", code, accountCode);
    }

    function testSuccessfulChildSelfdestructBeneficiaryWarmsParentFrameParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"734000000000000000000000000000000000000004ff";
        runAccessWarmthCase("successful-child-selfdestruct-beneficiary-warms-parent-frame", code, accountCode);
    }

    function testRevertedChildSelfdestructBeneficiaryRollsBackWarmthParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f150734000000000000000000000000000000000000004315f5260205ff3";
        bytes memory accountCode = hex"5f5f5f5f5f733000000000000000000000000000000000000003620f4240f15f5ffd";
        bytes memory destructeeCode = hex"734000000000000000000000000000000000000004ff";
        runAccessWarmthCaseWithSecondAccount(
            "reverted-child-selfdestruct-beneficiary-rolls-back-warmth", code, accountCode, destructeeCode
        );
    }

    function testSuccessfulChildCreateWarmsParentFrameParity() public {
        bytes memory accountCode = hex"60015f5ff05000";
        vm.etch(WORKER, accountCode);
        bytes memory preimage = createAddressPreimage(WORKER, vm.getNonce(WORKER));
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = abi.encodePacked(
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15073",
            expectedCreated,
            hex"315f5260205ff3"
        );
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runAccessWarmthCaseWithExpectedCreatedAccount(
            "successful-child-create-warms-parent-frame", code, accountCode, expectedCreated, keccaks
        );
    }

    function testRevertedChildCreateRollsBackCreatedAddressWarmthParity() public {
        bytes memory accountCode = hex"60015f5ff0505f5ffd";
        vm.etch(WORKER, accountCode);
        bytes memory preimage = createAddressPreimage(WORKER, vm.getNonce(WORKER));
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = abi.encodePacked(
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15073",
            expectedCreated,
            hex"315f5260205ff3"
        );
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runAccessWarmthCaseWithExpectedCreatedAccount(
            "reverted-child-create-rolls-back-created-address-warmth", code, accountCode, expectedCreated, keccaks
        );
    }

    function testSuccessfulChildCreate2WarmsParentFrameParity() public {
        bytes memory initCode = hex"00";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(WORKER, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = abi.encodePacked(
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15073",
            expectedCreated,
            hex"315f5260205ff3"
        );
        bytes memory accountCode = hex"5f60015f5ff55000";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runAccessWarmthCaseWithExpectedCreatedAccount(
            "successful-child-create2-warms-parent-frame", code, accountCode, expectedCreated, keccaks
        );
    }

    function testRevertedChildCreate2RollsBackCreatedAddressWarmthParity() public {
        bytes memory initCode = hex"00";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(0);
        bytes memory preimage = create2AddressPreimage(WORKER, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        bytes memory code = abi.encodePacked(
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15073",
            expectedCreated,
            hex"315f5260205ff3"
        );
        bytes memory accountCode = hex"5f60015f5ff5505f5ffd";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runAccessWarmthCaseWithExpectedCreatedAccount(
            "reverted-child-create2-rolls-back-created-address-warmth", code, accountCode, expectedCreated, keccaks
        );
    }

    function testSuccessfulChildStorageAccessWarmsLaterCallParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15060015f5360205f60015f5f732000000000000000000000000000000000000002620f4240f15060205ff3";
        bytes memory accountCode = hex"366008575f5450005b5f545f5260205ff3";
        runAccessWarmthCase("successful-child-storage-access-warms-later-call", code, accountCode);
    }

    function testRevertedChildStorageAccessRollsBackWarmthParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15060015f5360205f60015f5f732000000000000000000000000000000000000002620f4240f15060205ff3";
        bytes memory accountCode = hex"36600a575f54505f5ffd5b5f545f5260205ff3";
        runAccessWarmthCase("reverted-child-storage-access-rolls-back-warmth", code, accountCode);
    }

    function runAccessWarmthCase(string memory name, bytes memory code, bytes memory accountCode) internal {
        string[] memory keccaks = new string[](0);
        runAccessWarmthCaseDetailed(name, code, accountCode, false, hex"", false, address(0), keccaks);
    }

    function runAccessWarmthCaseWithSecondAccount(
        string memory name,
        bytes memory code,
        bytes memory accountCode,
        bytes memory secondAccountCode
    ) internal {
        string[] memory keccaks = new string[](0);
        runAccessWarmthCaseDetailed(name, code, accountCode, true, secondAccountCode, false, address(0), keccaks);
    }

    function runAccessWarmthCaseWithExpectedCreatedAccount(
        string memory name,
        bytes memory code,
        bytes memory accountCode,
        address expectedCreated,
        string[] memory keccaks
    ) internal {
        runAccessWarmthCaseDetailed(name, code, accountCode, false, hex"", true, expectedCreated, keccaks);
    }

    function runAccessWarmthCaseDetailed(
        string memory name,
        bytes memory code,
        bytes memory accountCode,
        bool hasSecondAccount,
        bytes memory secondAccountCode,
        bool hasExpectedCreated,
        address expectedCreated,
        string[] memory keccaks
    ) internal {
        address target = installRuntime(code);
        vm.etch(WORKER, accountCode);
        if (hasSecondAccount) {
            vm.etch(DESTRUCTEE, secondAccountCode);
        }
        uint64 workerNonce = vm.getNonce(WORKER);

        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        AccessWarmthVm.Gas memory gas = vm.lastCallGas();

        string[] memory command =
            new string[](49 + (hasSecondAccount ? 6 : 0) + (hasExpectedCreated ? 10 : 0) + 2 * keccaks.length);
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
        command[43] = "--account";
        command[44] = string.concat(addressArg(WORKER), "=", hexString(accountCode));
        command[45] = "--warm-address";
        command[46] = addressArg(WORKER);
        command[47] = "--expect-account-code";
        command[48] = string.concat(addressArg(WORKER), "=", hexString(accountCode));
        uint256 cursor = 49;
        if (hasSecondAccount) {
            command[cursor++] = "--account";
            command[cursor++] = string.concat(addressArg(DESTRUCTEE), "=", hexString(secondAccountCode));
            command[cursor++] = "--warm-address";
            command[cursor++] = addressArg(DESTRUCTEE);
            command[cursor++] = "--expect-account-code";
            command[cursor++] = string.concat(addressArg(DESTRUCTEE), "=", hexString(secondAccountCode));
        }
        if (hasExpectedCreated) {
            command[cursor++] = "--account-nonce";
            command[cursor++] = string.concat(addressArg(WORKER), "=", uintToString(workerNonce));
            command[cursor++] = "--expect-account-nonce";
            command[cursor++] = string.concat(addressArg(WORKER), "=", uintToString(vm.getNonce(WORKER)));
        }
        for (uint256 i = 0; i < keccaks.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccaks[i];
        }
        if (hasExpectedCreated) {
            command[cursor++] = "--expect-account-balance";
            command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreated.balance));
            command[cursor++] = "--expect-account-nonce";
            command[cursor++] =
                string.concat(addressArg(expectedCreated), "=", uintToString(vm.getNonce(expectedCreated)));
            command[cursor++] = "--expect-account-code";
            command[cursor++] = string.concat(addressArg(expectedCreated), "=", hexString(expectedCreated.code));
        }

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

    function addressArg(address value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function wordHex(bytes32 value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
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
