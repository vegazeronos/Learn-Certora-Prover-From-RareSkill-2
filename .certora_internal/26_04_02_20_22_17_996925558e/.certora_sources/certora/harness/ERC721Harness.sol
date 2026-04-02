// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ERC721} from "../../contracts/token/ERC721/ERC721.sol";

contract ERC721Harness is ERC721{

    constructor(string memory _name, string memory _symbol) ERC721(_name, _symbol){

    }

    function mint(address to, uint256 tokenId) external{
        _mint(to, tokenId);
    }

    function burn(uint256 tokenId) external{
        _burn(tokenId);
    }

}