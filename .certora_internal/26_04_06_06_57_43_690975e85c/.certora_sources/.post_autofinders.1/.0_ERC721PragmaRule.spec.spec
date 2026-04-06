methods{
    function balanceOf(address owner) external returns (uint256) envfree;
    function ownerOf(uint256 tokenId) external returns (address) envfree;
    function unsafeOwnerOf(uint256 tokenId) external returns (address) envfree;
    function unsafeGetApproved(uint256 tokenId) external returns(address) envfree;
    function isApprovedForAll(address owner, address operator) external returns (bool) envfree;
    function _.onERC721Received(address, address, uint256, bytes) external => DISPATCHER(true);
    
    function mint(address to, uint256 tokenId) external;
    function safeMint(address to, uint256 tokenId) external;
    function safeMint(address to, uint256 tokenId, bytes memory data) external;

    function burn(uint256 tokenId) external;

    function transferFrom(address from, address to, uint256 tokenId) external;
    function safeTransferFrom(address from, address to, uint256 tokenId) external;
    function safeTransferFrom(address from, address to, uint256 tokenId, bytes memory data) external;

    function approve(address to, uint256 tokenId) external;
    function setApprovalForAll(address operator, bool approved) external;
}


definition nonpayable(env e) returns bool = e.msg.value == 0;
definition nonzerosender(env e) returns bool = e.msg.sender != 0;
definition balanceLimit(address owner) returns bool = balanceOf(owner) < max_uint256;


// ghost for _owner => track how much token owner have
ghost mapping (address => mathint) g_owner{
    init_state axiom forall address a. g_owner[a] == 0; 
}

ghost mathint g_totalSumOwner{
    init_state axiom g_totalSumOwner == 0;
}

hook Sstore _owners[KEY uint256 tokenId] address newOwner(address oldOwner){
    g_owner[newOwner] = g_owner[newOwner] + to_mathint(newOwner != 0 ? 1 : 0);
    g_owner[oldOwner] = g_owner[oldOwner] - to_mathint(oldOwner != 0 ? 1 : 0);
    g_totalSumOwner = g_totalSumOwner + to_mathint(newOwner != 0 ? 1 : 0) - to_mathint(oldOwner != 0 ? 1 : 0);
}

// ghost for balances => track how much balances owner have?
ghost mapping(address => mathint) g_balances{
    init_state axiom forall address a. g_balances[a] == 0;
}

ghost mathint g_supply{
    init_state axiom g_supply == 0;
}

hook Sload uint256 balances _balances[KEY address owner]{
    require g_balances[owner] == to_mathint(balances);
}

hook Sstore _balances[KEY address owner] uint256 newBalance (uint256 oldBalance){
    g_supply = g_supply + newBalance - oldBalance;
}

//TODO: _balance == balanceOf(address) == _owner
invariant balanceOfConsistency(address owner)
    to_mathint(balanceOf(owner)) == g_balances[owner] &&
    to_mathint(balanceOf(owner)) == g_owner[owner];

//TODO: if owner(tokenid) is not 0, then balanceof(owner) > 0
invariant ownerHaveBalances(uint256 tokenId)
    unsafeOwnerOf(tokenId) != 0 => balanceOf(ownerOf(tokenId)) > 0
{
    preserved{
        requireInvariant balanceOfConsistency(ownerOf(tokenId));
    }
}

//TODO: the owned total equals to sum of balances
invariant supplyEqualsToSumBalances()
    g_supply == g_totalSumOwner
{
    preserved mint(address to, uint256 tokenId) with (env e){
        require balanceLimit(to);
    }
    preserved safeMint(address to, uint256 tokenId) with (env e){
        require balanceLimit(to);
    }
    preserved safeMint(address to, uint256 tokenId, bytes data) with (env e){
        require balanceLimit(to);
    }
    preserved burn(uint256 tokenId) with (env e){
        requireInvariant ownerHaveBalances(tokenId);
    }
    preserved transferFrom(address from, address to, uint256 tokenId) with (env e){
        require balanceLimit(to);
        requireInvariant ownerHaveBalances(tokenId);
    }
    preserved safeTransferFrom(address from, address to, uint256 tokenId) with (env e){
        require balanceLimit(to);
        requireInvariant ownerHaveBalances(tokenId);
    }
    preserved safeTransferFrom(address from, address to, uint256 tokenId, bytes data) with (env e){
        require balanceLimit(to);
        requireInvariant ownerHaveBalances(tokenId);
    }
}

//TODO: unminted token (unsafeOwner(tokenId) == 0) => approval(owner(tokenId)) == 0
invariant unmintedTokenNoApproval(uint256 tokenId)
    unsafeOwnerOf(tokenId) == 0 => unsafeGetApproved(tokenId) == 0;

invariant zeroAddressHasNoApprovedOperator (address operator)
    !isApprovedForAll(0, operator)
{
    preserved with (env e){
        require nonzerosender(e);
    }
}

//HELPER
//TODO: create helper soundness
// create each specific for each function mint, safeMint, safeMint, transferFrom, safeTransferFrom, safeTransferFrom, burn
function helperSoundFnCall(env e, method f){
    if(f.selector == sig:mint(address, uint256).selector){
        address to; uint256 tokenId;
        require balanceLimit(to);
        mint(e, to, tokenId);
    }else if(f.selector == sig:safeMint(address, uint256).selector){
        address to; uint256 tokenId;
        require balanceLimit(to);
        safeMint(e, to, tokenId);
    }else if(f.selector == sig:safeMint(address, uint256, bytes).selector){
        address to; uint256 tokenId; bytes data;
        require balanceLimit(to);
        require data.length < 0xffff;
        safeMint(e, to, tokenId, data);
    }else if(f.selector == sig:burn(uint256).selector){
        uint256 tokenId;
        requireInvariant ownerHaveBalances(tokenId);
        burn(e, tokenId);
    }else if(f.selector == sig:transferFrom(address, address, uint256).selector){
        address from; address to; uint256 tokenId;
        requireInvariant ownerHaveBalances(tokenId);
        require balanceLimit(to);
        transferFrom(e, from, to, tokenId);
    }else if(f.selector == sig:safeTransferFrom(address, address, uint256).selector){
        address from; address to; uint256 tokenId;
        requireInvariant ownerHaveBalances(tokenId);
        require balanceLimit(to);
        safeTransferFrom(e, from, to, tokenId);
    }else if(f.selector == sig:safeTransferFrom(address, address, uint256, bytes).selector){
        address from; address to; uint256 tokenId; bytes data;
        requireInvariant ownerHaveBalances(tokenId);
        require balanceLimit(to);
        require data.length < 0xffff;
        safeTransferFrom(e, from, to, tokenId, data);
    }else {
        calldataarg args;
        f(e, args);
    }
}


rule partialParamsRule(env e, method f, calldataarg args){
    satisfy true;
}