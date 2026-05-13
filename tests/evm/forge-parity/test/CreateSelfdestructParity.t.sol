// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface MiniVm {
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
}

contract CreateSelfdestructHashFactory {
    function createKillAndHash() external returns (bytes32 codeHash, uint256 codeSize) {
        bytes memory initCode = hex"6016600a5f3960165ff3732000000000000000000000000000000000000002ff";
        address created;
        assembly {
            created := create(0, add(initCode, 32), mload(initCode))
        }
        require(created != address(0), "create failed");
        (bool ok,) = created.call("");
        require(ok, "selfdestruct call failed");
        codeHash = created.codehash;
        codeSize = created.code.length;
    }

    function createKillAndCallAgain()
        external
        returns (
            bool firstOk,
            uint256 firstSize,
            bool secondOk,
            uint256 secondSize,
            uint256 secondWord,
            uint256 codeSize
        )
    {
        bytes memory initCode =
            hex"6024600a5f3960245ff33615600d57602a5f5260205ff35b732000000000000000000000000000000000000002ff";
        address created;
        assembly {
            created := create(0, add(initCode, 32), mload(initCode))
        }
        require(created != address(0), "create failed");
        bytes memory firstOut;
        (firstOk, firstOut) = created.call("");
        bytes memory secondOut;
        (secondOk, secondOut) = created.call(hex"01");
        firstSize = firstOut.length;
        secondSize = secondOut.length;
        if (secondOut.length >= 32) {
            assembly {
                secondWord := mload(add(secondOut, 32))
            }
        }
        codeSize = created.code.length;
    }

    function create2KillThenCreate2SameSalt()
        external
        returns (address first, bool killedOk, address second, uint256 codeSize)
    {
        bytes memory initCode = hex"6016600a5f3960165ff3732000000000000000000000000000000000000002ff";
        bytes32 salt = bytes32(uint256(0x1234));
        assembly {
            first := create2(0, add(initCode, 32), mload(initCode), salt)
        }
        require(first != address(0), "first create2 failed");
        (killedOk,) = first.call("");
        require(killedOk, "selfdestruct call failed");
        assembly {
            second := create2(0, add(initCode, 32), mload(initCode), salt)
        }
        codeSize = first.code.length;
    }
}

contract CreateSelfdestructParityTest {
    MiniVm internal constant vm = MiniVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testCreateThenSelfdestructDeletesCreatedAccountParity() public {
        bytes memory code =
            hex"6020601d5f395f5f5f5f5f60205f610309f0620f4240f15f5260205ff36016600a5f3960165ff3732000000000000000000000000000000000000002ff";
        bytes memory runtimeCode = hex"732000000000000000000000000000000000000002ff";
        runCreateSelfdestructCase("create-then-selfdestruct", code, runtimeCode, 777, WORKER);
    }

    function testCreateThenSelfdestructToSelfBurnsCreatedBalanceParity() public {
        bytes memory code = hex"600c601d5f395f5f5f5f5f600c5f610309f0620f4240f15f5260205ff36002600a5f3960025ff330ff";
        bytes memory runtimeCode = hex"30ff";
        runCreateSelfdestructCase("create-then-selfdestruct-self", code, runtimeCode, 777, address(0));
    }

    function testCreateThenSelfdestructExtcodehashRemainsVisibleInFrameParity() public {
        bytes memory code = type(CreateSelfdestructHashFactory).runtimeCode;
        bytes memory data = abi.encodeCall(CreateSelfdestructHashFactory.createKillAndHash, ());
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        bytes memory runtimeCode = hex"732000000000000000000000000000000000000002ff";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        keccaks[1] = keccakArg(runtimeCode, keccak256(runtimeCode));
        runCreateHashCase("create-then-selfdestruct-extcodehash-visible-in-frame", code, data, rootNonce, keccaks);
    }

    function testCreateThenSelfdestructCanCallAgainInFrameParity() public {
        bytes memory code = type(CreateSelfdestructHashFactory).runtimeCode;
        bytes memory data = abi.encodeCall(CreateSelfdestructHashFactory.createKillAndCallAgain, ());
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, rootNonce);
        bytes memory runtimeCode = hex"3615600d57602a5f5260205ff35b732000000000000000000000000000000000000002ff";
        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        keccaks[1] = keccakArg(runtimeCode, keccak256(runtimeCode));
        runCreateHashCase("create-then-selfdestruct-callable-in-frame", code, data, rootNonce, keccaks);
    }

    function testCreate2ThenSelfdestructSameSaltCollidesInFrameParity() public {
        bytes memory code = type(CreateSelfdestructHashFactory).runtimeCode;
        bytes memory data = abi.encodeCall(CreateSelfdestructHashFactory.create2KillThenCreate2SameSalt, ());
        uint64 rootNonce = vm.getNonce(TARGET);
        bytes memory initCode = hex"6016600a5f3960165ff3732000000000000000000000000000000000000002ff";
        bytes32 initHash = keccak256(initCode);
        bytes32 salt = bytes32(uint256(0x1234));
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        bytes memory runtimeCode = hex"732000000000000000000000000000000000000002ff";
        string[] memory keccaks = new string[](3);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        keccaks[2] = keccakArg(runtimeCode, keccak256(runtimeCode));
        runCreateHashCase("create2-then-selfdestruct-same-salt-collides-in-frame", code, data, rootNonce, keccaks);
    }

    function runCreateSelfdestructCase(
        string memory name,
        bytes memory code,
        bytes memory createdRuntimeCode,
        uint256 initialBalance,
        address expectedBeneficiary
    ) internal {
        address target = installRuntime(code);
        vm.deal(target, initialBalance);

        uint64 rootNonce = vm.getNonce(target);
        bytes memory preimage = createAddressPreimage(target, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));
        address beneficiary = expectedBeneficiary == address(0) ? expectedCreated : expectedBeneficiary;

        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        MiniVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](65);
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
        command[43] = "--nonce";
        command[44] = uintToString(rootNonce);
        command[45] = "--expect-nonce";
        command[46] = uintToString(vm.getNonce(target));
        command[47] = "--keccak";
        command[48] = keccakArg(preimage, keccak256(preimage));
        command[49] = "--keccak";
        command[50] = keccakArg(createdRuntimeCode, expectedCreated.codehash);
        command[51] = "--expect-account-balance";
        command[52] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreated.balance));
        command[53] = "--expect-account-code";
        command[54] = string.concat(addressArg(expectedCreated), "=0x");
        command[55] = "--expect-account-codehash";
        command[56] = string.concat(addressArg(expectedCreated), "=", wordHex(expectedCreated.codehash));
        command[57] = "--expect-account-nonce";
        command[58] = string.concat(addressArg(expectedCreated), "=", uintToString(vm.getNonce(expectedCreated)));
        command[59] = "--expect-account-balance";
        command[60] = string.concat(addressArg(beneficiary), "=", uintToString(beneficiary.balance));
        command[61] = "--expect-account-code";
        command[62] = string.concat(addressArg(beneficiary), "=0x");
        command[63] = "--expect-account-nonce";
        command[64] = string.concat(addressArg(beneficiary), "=", uintToString(vm.getNonce(beneficiary)));

        vm.ffi(command);
    }

    function runCreateHashCase(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint64 rootNonce,
        string[] memory keccakAssignments
    ) internal {
        address target = installRuntime(code);

        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        MiniVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](47 + 2 * keccakAssignments.length);
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
        command[43] = "--nonce";
        command[44] = uintToString(rootNonce);
        command[45] = "--expect-nonce";
        command[46] = uintToString(vm.getNonce(target));

        uint256 cursor = 47;
        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }

        vm.ffi(command);
    }

    function installRuntime(bytes memory code) internal returns (address target) {
        target = TARGET;
        vm.etch(target, code);
        require(target.code.length == code.length, "runtime not installed");
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

    function keccakArg(bytes memory data, bytes32 hash) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", wordHex(hash));
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
