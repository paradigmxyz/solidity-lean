// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinVestingAddress,
    OpenZeppelinVestingMockToken,
    OpenZeppelinVestingRejectEther,
    OpenZeppelinVestingSafeERC20,
    OpenZeppelinVestingWallet
} from "../src/OpenZeppelinVestingWallet.sol";

interface Vm {
    function warp(uint256 timestamp) external;
}

contract OpenZeppelinVestingWalletForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    uint256 public receivedEther;

    receive() external payable {
        receivedEther += msg.value;
    }

    function _expectCustom(bytes memory actual, bytes memory expected)
        private
        pure
    {
        require(keccak256(actual) == keccak256(expected), "custom error");
    }

    function testConstructorReceiveAndVestingMath() public {
        vm.warp(100);
        OpenZeppelinVestingWallet wallet =
            new OpenZeppelinVestingWallet{value: 10}(address(this), 100, 100);

        require(wallet.owner() == address(this), "owner");
        require(wallet.start() == 100, "start");
        require(wallet.duration() == 100, "duration");
        require(wallet.end() == 200, "end");
        require(wallet.released() == 0, "released");

        (bool ok, ) = address(wallet).call{value: 30}("");
        require(ok, "receive");
        require(address(wallet).balance == 40, "balance");

        vm.warp(99);
        require(wallet.releasable() == 0, "before start");
        require(wallet.vestedAmount(uint64(99)) == 0, "vested before");

        vm.warp(150);
        require(wallet.releasable() == 20, "half releasable");
        require(wallet.vestedAmount(uint64(150)) == 20, "half vested");

        vm.warp(200);
        require(wallet.releasable() == 40, "end releasable");
        require(wallet.vestedAmount(uint64(200)) == 40, "end vested");
    }

    function testReleaseEtherAtHalfAndEnd() public {
        OpenZeppelinVestingWallet wallet =
            new OpenZeppelinVestingWallet{value: 100}(address(this), 100, 100);

        vm.warp(150);
        wallet.release();
        require(wallet.released() == 50, "half released");
        require(address(wallet).balance == 50, "half balance");
        require(receivedEther == 50, "half received");

        vm.warp(200);
        wallet.release();
        require(wallet.released() == 100, "all released");
        require(address(wallet).balance == 0, "empty");
        require(receivedEther == 100, "all received");
    }

    function testReleaseEtherFailureRollsBack() public {
        OpenZeppelinVestingRejectEther rejecter =
            new OpenZeppelinVestingRejectEther();
        OpenZeppelinVestingWallet wallet =
            new OpenZeppelinVestingWallet{value: 10}(address(rejecter), 100, 100);

        vm.warp(200);
        try wallet.release() {
            revert("expected release failure");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(OpenZeppelinVestingAddress.FailedCall.selector)
            );
        }

        require(wallet.released() == 0, "rolled back");
        require(address(wallet).balance == 10, "funds kept");
    }

    function testReleaseERC20AtHalfAndEnd() public {
        OpenZeppelinVestingWallet wallet =
            new OpenZeppelinVestingWallet(address(this), 100, 100);
        OpenZeppelinVestingMockToken token = new OpenZeppelinVestingMockToken();
        token.mint(address(wallet), 100);

        vm.warp(150);
        require(wallet.releasable(address(token)) == 50, "token half releasable");
        wallet.release(address(token));
        require(wallet.released(address(token)) == 50, "token half released");
        require(token.balanceOf(address(this)) == 50, "token half received");
        require(token.balanceOf(address(wallet)) == 50, "token half balance");

        vm.warp(200);
        wallet.release(address(token));
        require(wallet.released(address(token)) == 100, "token all released");
        require(token.balanceOf(address(this)) == 100, "token all received");
        require(token.balanceOf(address(wallet)) == 0, "token empty");
    }

    function testReleaseERC20FailureRollsBack() public {
        OpenZeppelinVestingWallet wallet =
            new OpenZeppelinVestingWallet(address(this), 100, 100);
        OpenZeppelinVestingMockToken token = new OpenZeppelinVestingMockToken();
        token.mint(address(wallet), 10);
        token.setFailTransfer(true);

        vm.warp(200);
        try wallet.release(address(token)) {
            revert("expected token release failure");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinVestingSafeERC20.SafeERC20FailedOperation.selector,
                    address(token)
                )
            );
        }

        require(wallet.released(address(token)) == 0, "token rolled back");
        require(token.balanceOf(address(wallet)) == 10, "token kept");
        require(token.balanceOf(address(this)) == 0, "recipient unchanged");
    }
}
