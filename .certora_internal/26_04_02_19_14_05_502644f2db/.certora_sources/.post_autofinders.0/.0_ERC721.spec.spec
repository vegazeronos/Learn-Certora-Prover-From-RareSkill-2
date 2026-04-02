methods{
    function balanceOf(address owner) external returns (uint256) envfree;
    function ownerOf(uint256 tokenId) external returns (address) envfree;
    
    function mint(address to, uint256 tokenId) external;
    function burn(uint256 tokenId) external;
}

//TODO: verify mint success -> balance +, owner == minter,
rule mint_success(env e, address owner, uint256 tokenId){
    //precon
    mathint balanceOwnerBefore = balanceOf(owner);
    

    //action
    mint(e,owner, tokenId);

    //poststate
    mathint balanceOwnerAfter = balanceOf(owner);
    address ownerToken = ownerOf(tokenId);

    //assert
    assert balanceOwnerBefore + 1 == balanceOwnerAfter;
    assert ownerOf(tokenId) == ownerToken;
}

rule mint_revert(env e, address owner, uint256 tokenId){
    //precon
    mathint balanceOwnerBefore = balanceOf(owner);
    address ownerTokenBefore = ownerOf(tokenId);

    //action
    mint@withrevert(e, owner, tokenId);
    bool reverted = lastReverted;

    //poststate
    //assert
    assert reverted => (
        e.msg.value != 0 ||
        balanceOwnerBefore + 1 > max_uint256 ||
        owner == 0 ||
        ownerTokenBefore != 0
    );
}
//TODO: verify burn success -> balance -, owner == burner