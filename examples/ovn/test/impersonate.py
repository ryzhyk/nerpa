#! /usr/bin/env python
# -*-python-*-

# This is a Python tool that intercepts commands (command-lines) for
# ovn-nbctl or ovs-vsctl.  It can parse a subset of the commands
# and can either send them to the original tool or it can send the
# information to various other tools.

import sys
import subprocess
import re
import imp
import parglare   # parser generator
import ntpath
import ipaddress
import os
import string
import netaddr
import pickle
import csv
import itertools
import time

sys.setrecursionlimit(100000)

class PersistentStore:
    """Very simple key-value store.  Keys are strings, values are arbitrary Python objects."""
    def set(self, key, value):
        #print(key, "=", value)
        self.dict[key] = value

    def get(self, key):
        return self.dict[key]

    def __init__(self, storageFile):
        self.storageFile = storageFile
        self.dict = {}
        self.read()

    def clear(self):
        self.dict = {}

    def read(self):
        lines = []
        try:
            with open(self.storageFile, "r") as file:
                #print("Reading ", self.storageFile)
                reader = csv.reader(file)
                for k, v in reader:
                    vs = pickle.loads(v)
                    self.set(k, vs)
        except IOError:
            # The file does not exist yet; treat it as empty
            pass

    def write(self):
        with open(self.storageFile, "w") as file:
            writer = csv.writer(file)
            for (k, v) in self.dict.items():
                vs = pickle.dumps(v)
                writer.writerow([k, vs])

    def close(self):
        self.write()

# These are grammars in the parglare parser generator syntax for
# parsing (a subset of) the ovn-nbctl/ovs-vsctl command-line
# arguments.  The specification for the syntax is obtained from the
# man pages: https://www.mankier.com/8/ovn-nbctl and
# http://openvswitch.org/support/dist-docs/ovs-vsctl.8.txt

# We have three grammar fragments: a common fragment, and two
# extensions for ovn and ovs.

commonGrammar = r"""
KEYWORD:
/[\w-]+/  // keywords match on word boundaries
;

Arguments: GlobalOptions Options_command_args
;

GlobalOptions
: EMPTY
| GlobalOption GlobalOptions
;

Table
: Identifier
;

TableEntry
: Column OptKey "=" Value
| "'" Column OptKey "=" Value "'"
;

Column
: Identifier
;

Value
: SimpleValue
| SimpleValue "," Value
;

SimpleValue
: /([^,'" \r\n])+/
| /'[^']*'/
| /"[^"]*"/
;

OptKey
: EMPTY
| ":" Identifier
;


Address
: "'" EthAddress IpAddressList "'"
| '"' EthAddress IpAddressList '"'
| EthAddress IpAddressList
| "unknown"
| "dynamic"
| "router"
;

IpAddressList
: EMPTY
| IpAddress
| IpAddress IpAddressList
;

IpAddress
: Ipv4Address
| Ipv6Address
| "invalid"
;

Ipv4Address
: /((25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])\.){3}(25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])/ Netmask?
;

// TODO: This is incomplete, since it does not support embedded IPv4 addresses
Ipv6Address
: LongAddress Netmask?
;

// Same address as below
LongAddress
: /([0-9a-fA-F]{0,4}:){1,7}([0-9a-fA-F]{0,4})/
;

Netmask
: '/' Number
;

EthAddresses
: EMPTY
| EthAddress EthAddresses
;

EthAddress
: /[0-9a-fA-F]{2}:[0-9a-fA-F]{2}:[0-9a-fA-F]{2}:[0-9a-fA-F]{2}:[0-9a-fA-F]{2}:[0-9a-fA-F]{2}/
;

Port
: Identifier
;

PriorityMatch
: Priority Match
;

Verdict
: "allow"
| "deny"
| "reject"
| "drop"
| "allow-related"
;

Match
: Expression
;

Priority
: Number
;

Switch
: Identifier
| /'[^']*'/
| /"[^"]*"/
;

Router
: Identifier
;

Severity
: "alert"
| "warning"
| "notice"
| "info"
| "debug"
;

Identifier
: /\w[-_\d\w]*/
;

Expression
: "!" Expression   { 1 }
| "'" Expression "'"
| Symbol "[" Number "]"
| Symbol "[" Number ".." Number "]"
| "(" Expression ")"
| Symbol
| Symbol RelOp Constant
| Expression BoolOp Expression { left, 2 }
;

RelOp
: "=="
| "!="
| "<"
| ">"
| "<="
| ">="
;

BoolOp
: "&&"
| "||"
;

Symbol
: Identifier
| Symbol "." Identifier
;

Constant
: Number
| "{" ConstantList "}"
| String
| VariableName
;

VariableName
: "$" Identifier
;

ConstantList
: SimpleConstant
| SimpleConstant "," ConstantList
;

SimpleConstant
: Number
;

String
: /\"[^"]*\"/
;

Number
: /\d+/
| /0x[0-9a-fA-F]+/
;

Set
: "--if-exists"? "set" Table Record TableEntry+
;

Record
: "."
| Identifier
;
"""

ovnGrammar = commonGrammar + r"""
GlobalOption
: "--timeout=" Number
;

Options_command_args
: EMPTY
| "init"
| "show" Switch?
| LsAdd
| LsDel
| LsList
| LrAdd
| LrpAdd
| AclAdd
| AclDel
| AclList
| LspAdd
| LspDel
| LspList
| LspSetPortSecurity
| LspSetAddresses
| Create
| Set
;

Create
: CreateId? "create" Table TableEntry+
;

CreateId
: "--id=@" Identifier
;

LspSetAddresses
: "lsp-set-addresses" Port Addresses
;

Addresses
: EMPTY
| Address Addresses
;

LspSetPortSecurity
: "lsp-set-port-security" Port Addresses
;

LspDel
: "--if-exist"? "lsp-del" Port
;

LspList
: "lsp-list" Switch
;

LspAdd
: "--may-exist"? "lsp-add" Switch Port ParentAndTagRequest?
;

ParentAndTagRequest
: Parent TagRequest
;

Parent
: Identifier
;

TagRequest
: Number
;

AclList
: "acl-list" Switch
;

AclDel
: "acl-del" Switch Direction? PriorityMatch?
;

AclAdd
: AclAddOptions "acl-add" Switch Direction Priority Match Verdict
;

AclAddOptions
: EMPTY
| AclAddOption AclAddOptions
;

AclAddOption
: "--log"
| "--severity=" Severity
| "--name=" Identifier
| "--may-exist"
;

Direction
: "from-lport"
| "to-lport"
;

LrAdd
: LrAddOption "lr-add" Router?
;

LrAddOption
: EMPTY
| "--may-exist"
| "--add-duplicate"
;

LrpAdd
: "--may-exist"? "lrp-add" Router Port Address
;

LsAdd
: LsAddOption "ls-add" Switch?
;

LsAddOption
: EMPTY
| "--may-exist"
| "--add-duplicate"
;

LsDel
: LsDelOption "ls-del" Switch
;

LsDelOption
: EMPTY
| "--if-exists"
;

LsList
: "ls-list"
;

"""

ovsGrammar = commonGrammar + """
GlobalOption
: "--timeout=" Number
| "--no-wait"
| "--bare"
;

Options_command_args
: EMPTY
| AddBr
| DelBr
| AddPort
| Set
| "init"
| "show"
| Get
| Find
;

TableEntrySelector
: Column OptKey RelOpAndEq Value
;

RelOpAndEq
: RelOp
| "="
;

Find
: ColumnPrefixList? "find" Table TableEntrySelector
;

ColumnPrefixList
: "--columns" ColumnList
;

ColumnList
: Column
| Column "," ColumnList
;

AddPort
: "--may-exist"? "add-port" Bridge Port TableEntry*
;

AddBr
: "--may-exist"? "add-br" Bridge ParentVlan?
;

ParentVlan
: Parent Vlan
;

Parent
: Bridge
;

Vlan
: Number
;

DelBr
: "--if-exists"? "del-br" Bridge
;

Bridge
: Identifier
;

Get
: "--if-exists"? IdAt? "get" Table Record ColumnOptKey?
;

ColumnOptKey
: Column OptKey
;

IdAt
: "--id=@" Identifier
;

"""

valGrammar = """
Vals
: Value
;
""" + ovnGrammar

addressGrammar = """
Addr
: Address
;
""" + ovnGrammar

logfile = open(os.environ.get("LOGFILE"), 'a')
cocoon_path = os.environ.get("COCOON_PATH")
ovs_rundir = os.environ.get("OVS_RUNDIR")
storefile = os.environ.get("OVSHOME") + "/test.store"

def getHyhpervisor():
    return os.path.basename(os.path.normpath(ovs_rundir))


def getValueParser():
    g = parglare.Grammar.from_string(valGrammar)
    return parglare.Parser(g, build_tree=True)

def getAddressParser():
    g = parglare.Grammar.from_string(addressGrammar)
    return parglare.Parser(g, build_tree=True)


def cocoon(cmd):
    log("cocoon command: " + cmd)
    start_time = time.clock()
    proc = subprocess.Popen([cocoon_path, "--action=cmd"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (out, err) = proc.communicate(cmd)
    elapsed_time = time.clock() - start_time
    log("cocoon runtime: " + str(elapsed_time))
    log("cocoon stdout: " + out)
    log("cocoon stderr: " + err)

def ovs_vsctl(cmd):
    ovsHome = os.environ.get("OVSHOME")
    ovs = ovsHome + "utilities/ovs-vsctl"
    log("ovs_vsctl command: " + " ".join(cmd))
    output = subprocess.check_output([ovs] + cmd, stderr=subprocess.STDOUT).strip()
    log("ovs_vsctl output: " + output)
    return output

def log(str):
    logfile.write(str + '\n')

def convertIpToBytes(ipAddress):
    """
    Given an IPv4 or IPv6 address like 192.168.1.200 converts it into a byte string
    of hexadecimal values
    """
    add = ipaddress.ip_address(unicode(ipAddress))
    return format(int(add), 'x')

def parseOptions(parser, line):
    """
    Parse the command-line options using the indicated grammar.
    """
    log("Parsing " + line)
    result = parser.parse(line)
    log(result.tree_str())
    return result

def callOriginal(options):
    """
    Relay the call to the original program.
    """
    log("Calling " + " ".join(options))
    subprocess.call(options)

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "replay":
        # replay pre-recorded commands
        with open("commands.txt", "r") as file:
            commands = file.readlines()
            for cmd in commands:
                (impersonate, x, args) = cmd.partition(" ")
                doImpersonate(impersonate, args)
    elif len(sys.argv) > 1:
        impersonate = ntpath.basename(sys.argv[0])
        # Given arguments start impersonating the respective binary
        line = ""
        for arg in sys.argv[1:]:
            if " " in arg:
                arg = "'" + arg + "'"
            line += " " + arg
        
        with open("commands.txt", "a") as file:
            file.write(impersonate + ' ' + line + '\n')
        doImpersonate(impersonate, line)
    else:
        # otherwise just run tests
        test()

def doImpersonate(impersonate, line):
    ovsHome = os.environ.get("OVSHOME")
    originalCommand = None
    if impersonate == "ovn-nbctl":
        impersonateOVN(line)
    elif impersonate == "ovs-vsctl":
        originalCommand = ovsHome + "utilities/ovs-vsctl"
        options = [originalCommand] + sys.argv[1:]
        callOriginal(options)
        impersonateOVS(line)
    elif impersonate == "ovn-controller":
        # just block ovn-controller invocation
        return

def getOvnParser():
    g = parglare.Grammar.from_string(ovnGrammar)
    return parglare.Parser(g, build_tree=True)

def getOvsParser():
    g = parglare.Grammar.from_string(ovsGrammar)
    return parglare.Parser(g, build_tree=True)

def getField(node, field):
    return next(x for x in node.children if x.symbol.name == field)

def getList(node, field, fields):
    if len(node.children) == 0:
        return []
    else:
        f = getField(node, field)
        tail = getOptField(node, fields, None)
        if tail == None:
            return [f]
        else:
            fs = getList(tail, field, fields)
            return [f] + fs

def mkExpr(expr):
    if expr.children[0].symbol.name == "!":
        return "(not" + mkExpr(expr.children[1]) + ")"
    elif len(expr.children) == 4 and expr.children[1].symbol.name == "[":
        return mkSymbol(expr.children[0]) + "[" + expr.children[2].value + ":" + expr.children[2].value + "]"
    elif len(expr.children) == 6 and expr.children[3].symbol.name == "..":
        return mkSymbol(expr.children[0]) + "[" + expr.children[4].value + ":" + expr.children[2].value + "]"
    elif len(expr.children) == 3 and expr.children[1].symbol.name == "BoolOp":
        return "(" + mkExpr(expr.children[0]) + mkBoolOp(expr.children[1].children[0].value) + mkExpr(expr.children[2]) + ")"
    elif len(expr.children) == 3 and expr.children[1].symbol.name == "RelOp":
        return "(" + mkRelExpr(expr.children[0], expr.children[1].children[0].value, expr.children[2]) + ")"
    elif len(expr.children) == 1 and expr.children[0].symbol.name == "Symbol":
        return mkBoolSymbol(expr.children[0])
    elif len(expr.children) == 1 or len(expr.children) == 3:
        return mkExpr(getField(expr, 'Expression'))
    else:
        raise Exception('Invalid expression ' + expr.tree_str())

def mkBoolOp(op):
    if op == "&&":
        return "and"
    elif op == "||":
        return "or"
    else:
        raise Exception("unsupported boolean operation: " + op)

def mkRelOp(op):
    return  op

matchIP4 = ["EthPacket{_,_,_,_,_,_,EthIP4{ip4}}"]
matchIP6 = ["EthPacket{_,_,_,_,_,_,EthIP6{ip6}}"]
matchARP = ["EthPacket{_,_,_,_,_,_,EthARP{arp}}"]
matchTCP = [ "EthPacket{_,_,_,_,_,_,EthIP4{_,_,_,_,_,_,_,_,_,_,IPTCP{tcp}}}"
           , "EthPacket{_,_,_,_,_,_,EthIP6{_,_,_,_,_,_,_,IPTCP{tcp}}}"]
matchUDP = [ "EthPacket{_,_,_,_,_,_,EthIP4{_,_,_,_,_,_,_,_,_,_,IPUDP{udp}}}"
           , "EthPacket{_,_,_,_,_,_,EthIP6{_,_,_,_,_,_,_,IPUDP{udp}}}"]
matchICMP4 = ["EthPacket{_,_,_,_,_,_,EthIP4{_,_,_,_,_,_,_,_,_,_,IPICMP4{icmp}}}"]
matchICMP6 = ["EthPacket{_,_,_,_,_,_,EthIP6{_,_,_,_,_,_,_,IPICMP6{icmp}}}"]

symTable = { 'inport'         : [("p.portnum"                        , None)]
#           , 'flags.loopback' :
           , 'eth.src'        : [("p.src"                            , None)]
           , 'eth.dst'        : [("p.dst"                            , None)]
           , 'eth.type'       : [("p.ethtype"                        , None)]
#           , 'vlan.tci'       :
           , 'vlan.vid'       : [("p.vlan.vid"                       , None)]
           , 'vlan.pcp'       : [("p.vlan.pcp"                       , None)]
           , 'ip.proto'       : [("ip4.proto"                        , matchIP4)
                                ,("ip6.proto"                        , matchIP6)]
           , 'ip4.src'        : [("ip4.src"                          , matchIP4)]
           , 'ip4.dst'        : [("ip4.dst"                          , matchIP4)]
           , 'ip6.src'        : [("ip6.src"                          , matchIP6)]
           , 'ip6.dst'        : [("ip6.dst"                          , matchIP6)]
           , 'ip6.label'      : [("ip6.label"                        , matchIP6)]
#           , 'arp.op'         : []
           , 'arp.spa'        : [("arp.spa"                          , matchARP)]
           , 'arp.tpa'        : [("arp.tpa"                          , matchARP)]
           , 'arp.sha'        : [("arp.sha"                          , matchARP)]
           , 'arp.tha'        : [("arp.tha"                          , matchARP)]
           , 'tcp.src'        : [("tcp.src"                          , matchTCP)]
           , 'tcp.dst'        : [("tcp.dst"                          , matchTCP)]
           , 'udp.src'        : [("udp.src"                          , matchUDP)]
           , 'udp.dst'        : [("udp.dst"                          , matchUDP)]
           , 'icmp4.type'     : [("icmp.type"                        , matchICMP4)]
           , 'icmp4.code'     : [("icmp.code"                        , matchICMP4)]
           , 'icmp6.type'     : [("icmp.type"                        , matchICMP6)]
           , 'icmp6.code'     : [("icmp.code"                        , matchICMP6)]
#           , 'nd.target'      :
#           , 'nd.sll'         :
#           , 'nd.tll'         :
#           , 'ct_mark'        :
#           , 'ct_label'       :
#           , 'ct.trk'         :
#           , 'ct.new'         :
#           , 'ct.est'         :
#           , 'ct.rel'         :
#           , 'ct.rpl'         :
#           , 'ct.inv'         :

           , 'eth.bcast'      : [("p.dst == 48'hffffffffffff"       , None)]
           , 'eth.mcast'      : [("p.dst[40:40] == 1"               , None)]
#           , 'vlan.present'   :
           , 'ip4'            : [("true"                            , matchIP4)]
           , 'ip4.mcast'      : [("ip4.dst[31:28] == 4'he"          , matchIP4)]
           , 'ip6'            : [("true"                            , matchIP6)]
           , 'ip'             : [("true"                            , matchIP4)
                                ,("true"                            , matchIP6)]
           , 'icmp4'          : [("true"                            , matchICMP4)]
           , 'icmp6'          : [("true"                            , matchICMP6)]
           , 'icmp'           : [("true"                            , matchICMP4)
                                ,("true"                            , matchICMP6)]
           , 'arp'            : [("true"                            , matchARP)]
#           , 'nd'             :
#           , 'nd_ns'          :
#           , 'nd_na'          :
           , 'tcp'            : [("true"                            , matchTCP)]
           , 'udp'            : [("true"                            , matchUDP)]
#           , 'sctp'           :
           }

def mkBoolSymbol(sym):
    s = getSymbol(sym)
    if s in symTable:
        matches = []
        for (e, ms) in symTable[s]:
            if ms == None:
                return e
            else:
                for m in ms:
                    matches = matches + [m + ": " + e]
        return "match (p){" + ", ".join(matches + ["_ -> false"]) + "}"
    else:
        raise Exception("unsupported symbol: " + s)

def mkRelExpr(sym, op, const):
    o = mkRelOp(op)
    cs = mkConst(const)
    s = getSymbol(sym)
    exprs = []
    for c in cs:
        expr = ""
        if s == "inport":
            expr =  "lp" + o + mkLPortId(c[1:-1])
        elif s == "outport" and o == "==":
            expr = "lp" + o + mkLPortId(c[1:-1])
        elif s in symTable:
            if len(symTable[s]) == 1 and symTable[s][0][1] == None:
                expr = "(" + symTable[s][0][0] + o + c + ")"
            else:
                matches = []
                for (e, ms) in symTable[s]:
                    for m in ms:
                        matches = matches + [m + ": " + e + o + c]
                expr = "match (p){" + ", ".join(matches + ["_ -> false"]) + "}"
        else:
            raise Exception("unsupported symbol: " + s)
        exprs = exprs + [expr]
    return " or ".join(exprs)

def mkConst(const):
    sym = const.children[0].symbol.name
    if sym == 'Number':
        return ["'h%x" % int(const.children[0].children[0].value, 0)]
    elif sym == '{':
        return map(lambda x: "'h%x" % int(x.children[0].children[0].value, 0) , getList(const.children[1], 'SimpleConstant', 'ConstantList'))
    elif sym == 'String':
        return [const.children[0].value]
    elif sym == 'VariableName':
        store = PersistentStore(storefile)
        vals = store.get(const.children[0].children[1].value)
        store.close()
        #ovs_vsctl(["--columns=addresses", "find", "Address_Set", "name=" + const.children[0].children[1].value])
        log("address list: " + str(vals))
        #val_parser = getValueParser()
        #vals = val_parser.parse(addrs[addrs.find("[") + 1 : addrs.find("]")]).children[0]
        return map(lambda x: mkAddress(x[1:-1]), vals)
    else:
        raise Exception('Invalid constant ' + const.tree_str())

def getSymbol(sym):
    if sym.children[0].symbol.name == 'Identifier':
        return sym.children[0].value
    else:
        return getSymbol(sym.children[0]) + '.' + sym.children[2].value

def getConst(const):
    sym = const.children[0].symbol.name
    if sym == 'Number':
        return const.children[0].children[0].value
    elif sym == '{':
        return map(lambda x: x.children[0].children[0].value , getList(const.children[1], 'SimpleConstant', 'ConstantList'))
    elif sym == 'String':
        return const.children[0].value
    elif sym == 'VariableName':
        return '$' + const.children[0].children[1].value
    else:
        raise Exception('Invalid constant ' + const.tree_str())

def mkVerdict(v):
    if v == "allow":
        return "ACLAllow"
    elif v == "reject":
        return "ACLReject"
    elif v == "deny":
        return "ACLReject"
    elif v == "drop":
        return "ACLDrop"
    elif v == "allow-related":
        return "ACLAllowRelated"

def mkDirection(d):
    if d == "from-lport":
        return "ACLFrom"
    elif d == "to-lport":
        return "ACLTo"
    else:
        raise Exception("unsupported ACL direction :" + d)

def mkTunPortId(name):
    return mkId(name, 8)

def mkChassisId(cname):
    return mkId(cname, 4)

def mkVPortId(vname):
    return mkId(vname, 8)

def mkLPortId(lpname):
    return mkId(lpname[:8], 8)

def mkSwId(swname):
    return mkId(swname[-3:], 8)

def mkRtId(rname):
    return mkId(rname, 8)

def mkRPortId(pname):
    return mkId(pname[-4:], 4)

def mkId(name, w):
    if len(name) > w:
        raise Exception("mkId(" + name + "," + str(w) + "): identifier too long")
    return str(w*8)+ "'h" + "".join(map(lambda x: "%02x"%x, map(ord, list(name))))

def mkMACAddr(mac):
    return "48'h%x" % int(netaddr.EUI(mac))

def mkIPAddr(ip):
    if ip.children[0].symbol.name == 'Ipv4Address':
        return "IPAddr4{32'h%x}" % netaddr.IPNetwork(ip.children[0].children[0].value).ip
    elif ip.children[0].symbol.name == 'Ipv6Address':
        return "IPAddr6{128'h%x}" % netaddr.IPNetwork(ip.children[0].children[0].value).ip
    else:
        raise Exception("not implemented: mkIPAddr " + ip.children[0].symbol.name)

def mkAddress(addr):
    if netaddr.valid_mac(addr):
        return mkMACAddr(addr)
    elif netaddr.valid_ipv4(addr):
        return "IPAddr4{32'h%x}" % netaddr.IPAddress(addr)
    elif netaddr.valid_ipv6(addr):
        return "IPAddr6{128'h%x}" % netaddr.IPAddress(addr)
    else:
        raise Exception("unknown address format " + addr)

def mkIPSubnet(ip):
    netmask = getOptField(getField(ip.children[0], "Netmask_opt"), "Netmask", None)
    log("ip.children[0] label:" + ip.children[0].symbol.name)
    if netmask != None:
        log("netmask")
        log("mask:" + getField(netmask, "Number").children[0].value)
        subnet = ip.children[0].children[0].value + "/" + getField(netmask, "Number").children[0].value
    else:
        log("no netmask")
        subnet = ip.children[0].children[0].value
    net = netaddr.IPNetwork(subnet)
    if ip.children[0].symbol.name == 'Ipv4Address':
        mask = 0
        for i in range(32-int(net.prefixlen), 32):
            mask = mask + (1 << i)
        return "IPSubnet4{IP4Subnet{32'h%x,32'h%x}}" % (net.ip, mask)
    elif ip.children[0].symbol.name == 'Ipv6Address':
        mask = 0
        for i in range(128-int(net.prefixlen), 128):
            mask = mask + (1 << i)
        return "IPSubnet6{IP6Subnet{128'h%x,128'h%x}}" % (net.ip, mask)
    else:
        raise Exception("not implemented: mkIPSubnet " + ip.children[0].symbol.name)

def mkMACIPs(addr):
    mac = mkMACAddr(getField(addr, 'EthAddress').value)
    subnets = map(mkIPSubnet, getList(getField(addr, 'IpAddressList'), 'IpAddress', 'IpAddressList'))
    return (mac, subnets)

def getTableEntry(entry):
    col = getField(entry, 'Column').children[0].value
    okey = getField(entry, 'OptKey')
    key = None
    if len(okey.children) == 2:
        key = okey.children[1].value
    vals = map(lambda x: x.children[0].value, getList(getField(entry, 'Value'), 'SimpleValue', 'Value'))
    return (col, key, vals)

def formatTableEntry(e):
    (col, key, vals) = getTableEntry(e)
    skey = ""
    if key == None:
        skey = ""
    else:
        skey = ":" + key
    return col + skey + '=' + ",".join(vals)

def getOptField(node, field, default):
    for x in node.children:
        if x.symbol.name == field:
            return x
    return None

def allocZone():
    store = PersistentStore(storefile)
    z = 0
    try:
        z = store.get("_last_zone_id")
        if z == 32766:
            z = 0
    except:
        pass
    z = z+1
    store.set("_last_zone_id", z)
    store.close()
    return z

def impersonateOVN(line):
    parser = getOvnParser()
    parts = line.split(" -- ")
    log('\novn-nbctl' + line)
    cocooncmds = []
    for part in parts:
        cmd = None
        try:
            cmdargs = getField(parseOptions(parser, part), "Options_command_args")
            if len(cmdargs.children) == 0:
                continue
            cmd = cmdargs.children[0]
        except parglare.exceptions.ParseError as e:
            print "impersonateOVN: error parsing:", part, str(e)
            raise e

        log(cmd.tree_str())
        log('command symbol: ' + cmd.symbol.name)
        if cmd.symbol.name in ovnHandlers:
            cocooncmds += ovnHandlers[cmd.symbol.name](cmd)
        else:
            log('unknown command, ignoring')
    cocooncmd = ";\n".join(cocooncmds)
    if cocooncmd != "":
        cocoon(cocooncmd)

def getCommands(options):
    cmds = getField(options, 'Options_command_args')
    if len(cmds.children) == 0:
        return []
    else:
        first = getField(getField(cmds.children[0], 'FirstCommand'), 'OptionsCommand').children[0]
        rest = []
        lst = getOptField(cmds.children[0], 'SeparatedCommandsList', None)
        if lst != None:
            rest = map(lambda x: x.children[0], getList(lst, 'OptionsCommand', 'SeparatedCommandsList'))
        return [first] + rest


def ovnInit(cmd):
    log('init: nothing to do here')
    return []

def ovnLrAdd(cmd):
    ropt = getField(cmd, 'Router_opt')
    rname = getField(ropt, 'Router').children[0].value
    log('adding router ' + rname)
    return ['LogicalRouter.put(LogicalRouter{' + mkRtId(rname) + ', true, "' + rname + '", RouterRegular})']

def ovnLrpAdd(cmd):
    rt = getField(cmd, 'Router').children[0].value
    port = getField(cmd, 'Port').children[0].value
    addr = getField(cmd, 'Address')
    addr_str = addrStr(addr)
    (mac, subnets) = mkMACIPs(addr)
    zone = allocZone()
    cmds = ['LogicalRouterPort.put(LogicalRouterPort{' +
            ', '.join([mkRPortId(port), '"' + port + '"', mkRtId(rt), 'LRPRegular', mac, 'true', 'NoPeer', str(zone)]) + '})']
    for subnet in subnets: 
        cmds.append('LRouterPortNetwork.put(LRouterPortNetwork{' + ', '.join([mkRPortId(port), subnet]) + '})')
    return cmds

def ovnLsAdd(cmd):
    swopt = getField(cmd, 'Switch_opt')
    swname = getField(swopt, 'Switch').children[0].value
    log('adding switch ' + swname)
    return ['LogicalSwitch.put(LogicalSwitch{' + mkSwId(swname) + ', LSwitchRegular, "' + swname + '", NoSubnet})']

def ovnLspAdd(cmd):
    sw = getField(cmd, 'Switch').children[0].value
    port = getField(cmd, 'Port').children[0].value
    partag = getOptField(cmd, 'ParentAndTagRequest', None)
    par = None
    tag = None
    if partag != None:
        par = getField(partag, 'Parent').children[0].value
        tag = getField(partag, 'TagRequest').children[0].value
        raise Exception('not implemented: VIF ports')
    else:
        log('adding switch port ' + sw + ' ' + port)
        zone = allocZone()
        return ['LogicalSwitchPort.put(LogicalSwitchPort{' +
                ', '.join([mkLPortId(port), mkSwId(sw), 'LPortVM{}', '"'+port+'"', 'true', 'NoDHCP4Options', 'NoDHCP6Options', 'false', str(zone)]) + '})']

def ovnLspSetAddresses(cmd):
    port = getField(cmd, 'Port').children[0].value
    addrs = getList(getField(cmd, 'Addresses'), 'Address', 'Addresses')
    addr_strs = map(addrStr, addrs)
    log('adding switch port addresses ' + port + ' ' + ','.join(addr_strs))
    return doOvnLspSetAddresses(port, addrs)

def doOvnLspSetAddresses(port, addrs):
    #cmds = ["{LogicalSwitchPortMAC.delete(?.lport==" + mkLPortId(port) + "); LogicalSwitchPortIP.delete(?.lport==" + mkLPortId(port) + ")}"]
    cmds = []
    for addr in addrs:
        addrtype = addr.children[0].symbol.name
        if addrtype == "unknown":
            cmds.append("the (lp in LogicalSwitchPort | lp.id == " + mkLPortId(port)+ ") {LogicalSwitchPort.delete(?.id == lp.id); lp.unknown_addr=true; LogicalSwitchPort.put(lp)}")
        elif addrtype == "dynamic":
            #cocoon("LogicalSwitchPortDynAddr.put(LogicalSwitchPortDynAddr{" + ", ".join([???, mkId(port, 8), "0", "NoIPAddr"]) + "})")
            raise Exception("not implemented: lsp-set-addresses dynamic")
        elif addrtype == "router":
            raise Exception("not implemented: lsp-set-addresses router")
        else:
            mac = mkMACAddr(getField(addr, 'EthAddress').value)
            cmds.append("LogicalSwitchPortMAC.put(LogicalSwitchPortMAC{" + mkLPortId(port) + ", " + mac + "})")
            ips = map(mkIPAddr,
                      itertools.takewhile(lambda x: x.children[0].symbol.name != "invalid",
                                          getList(getField(addr, 'IpAddressList'), 'IpAddress', 'IpAddressList')))
            log("ips: " + str(ips))
            for ip in ips:
                cmds.append("LogicalSwitchPortIP.put(LogicalSwitchPortIP{" + mkLPortId(port) + ", " + mac + ", " + ip + "})")
    return cmds

def addrStr(addr):
    if addr.children[0].symbol.name == "unknown":
        return "unknown"
    elif addr.children[0].symbol.name == "dynamic":
        return "dynamic"
    elif addr.children[0].symbol.name == "router":
        return "router"
    else:
        eth = getField(addr, 'EthAddress').value
        ips = map(ipStr, getList(getField(addr, 'IpAddressList'), 'IpAddress', 'IpAddressList'))
        return " ".join([eth] + ips)

def ipStr(ip):
    if ip.children[0].symbol.name == 'invalid':
        return 'invalid'
    else:
        return ip.children[0].children[0].value

def ovnLspSetPortSecurity(cmd):
    port = getField(cmd, 'Port').children[0].value
    addrs = getList(getField(cmd, 'Addresses'), 'Address', 'Addresses')
    addr_strs = map(addrStr, addrs)
    #for addr in addrs:
    log('lsp-set-port-security ' + port + ' ' + ','.join(addr_strs))
    cmds = []
    for addr in addrs:
        (mac, subnets) = mkMACIPs(addr) 
        cmds.append("PortSecurityMAC.put(PortSecurityMAC{" + mkLPortId(port) + ", " + mac + "})")
        log("subnets: " + str(subnets))
        for subnet in subnets:
            cmds.append("PortsecurityIP.put(PortSecurityIP{" + mkLPortId(port) + ", " + mac + ", " + subnet + "})")
    return cmds

def ovnAclAdd(cmd):
    sw        = getField(cmd, 'Switch').children[0].value
    direction = mkDirection(getField(cmd, 'Direction').children[0].value)
    prio      = getField(cmd, 'Priority').children[0].children[0].value
    match     = mkExpr(getField(cmd, 'Match').children[0])
    verdict   = mkVerdict(getField(cmd, 'Verdict').children[0].value)
    log('acl-add ' + ' '.join([sw, direction, prio, match, verdict]))
    return ["ACL.put(ACL{" + ", ".join([mkSwId(sw), prio, direction, "\\(p:Packet, lp:lport_id_t): bool =" + match, verdict])  + "})"]

def ovnCreate(cmd):
    table = getField(cmd, 'Table').children[0].value
    entries = getList(getField(cmd, 'TableEntry_1'), 'TableEntry', 'TableEntry_1')
    d = dict(map(lambda x: (x[0], x[2]), map(getTableEntry, entries)))
    if table == "Address_Set":
        key = d['name'][0]
        vals = d['addresses']
        store = PersistentStore(storefile)
        store.set(key, vals)
        store.close()
    log('create ' + table + ' ' + ' '.join(map(formatTableEntry, entries)))
    return []

def ovnSet(cmd):
    table = getField(cmd, 'Table').children[0].value
    record = getField(cmd, 'Record').children[0].value
    entries = getList(getField(cmd, 'TableEntry_1'), 'TableEntry', 'TableEntry_1')
    log("set " + table + ' ' + record + ' ' + ' '.join(map(formatTableEntry, entries)))
    if table == "Logical_Switch_Port":
        return ovnSetLSP(record, entries)
    else:
        return []

def ovnSetLSP(port, entries):
    d = dict(map(lambda x: ((x[0], x[1]), x[2]), map(getTableEntry, entries)))
    cmds=[]
    if ('type', None) in d:
        if d[('type', None)] == ['router']:
            if ('options', 'router-port') in d:
                rp = d[('options', 'router-port')][0]
                #cocoon("the (lp in LogicalSwitchPort | lp.id == " + mkLPortId(port)+ ") {LogicalSwitchPort.delete(?.id == lp.id); lp.ptype=LPortRouter{" + mkRPortId(rp) + "}; LogicalSwitchPort.put(lp)}")
                cmds.append("the (lp in LogicalSwitchPort | lp.id == " + mkLPortId(port)+ ") {LogicalSwitchPort.delete(?.id == lp.id); lp.ptype=LPortRouter{" + mkRPortId(rp) + "}; LogicalSwitchPort.put(lp)}")
    if ('addresses', None) in d:
        addr_parser = getAddressParser()
        addrs = map(lambda x: addr_parser.parse(x).children[0], d[('addresses', None)])
        cmds += doOvnLspSetAddresses(port, addrs)
    return cmds

ovnHandlers = { 'init'               : ovnInit
              , 'LsAdd'              : ovnLsAdd
              , 'LspAdd'             : ovnLspAdd
              , 'LspSetAddresses'    : ovnLspSetAddresses
              , 'LspSetPortSecurity' : ovnLspSetPortSecurity
              , 'AclAdd'             : ovnAclAdd
              , 'Create'             : ovnCreate
              , 'LrAdd'              : ovnLrAdd
              , 'LrpAdd'             : ovnLrpAdd
              , 'Set'                : ovnSet
              }

def impersonateOVS(line):
    log('\novs-vsctl' + line)
    parser = getOvsParser()
    parts = line.split(" -- ")
    cocooncmds = []
    for part in parts:
        cmd = None
        try:
            cmdargs = getField(parseOptions(parser, part), "Options_command_args")
            if len(cmdargs.children) == 0:
                continue
            cmd = cmdargs.children[0]
        except parglare.exceptions.ParseError as e:
            print "impersonateOVS: error parsing:", part, str(e)
            raise e

        log(cmd.tree_str())
        log('command symbol: ' + cmd.symbol.name)
        if cmd.symbol.name in ovsHandlers:
            cocooncmds += ovsHandlers[cmd.symbol.name](cmd)
        else:
            log('unknown command, ignoring')
    cocooncmd = ";\n".join(cocooncmds)
    if cocooncmd != "":
        cocoon(cocooncmd)

def ovsAddBr(cmd):
    br = getField(cmd, 'Bridge').children[0].value
    opvlan = getField(cmd, 'ParentVlan_opt')
    par = None
    vlan = None
    if len(opvlan.children) != 0:
        par = getField(opvlan, 'Parent').children[0].children[0].value
        vlan = getField(opvlan, 'Vlan').children[0].children[0].value
        raise Exception("not supported: fake bridges")
    log("add-br " + br + str(par) + ' ' + str(vlan))
    if br == "br-int":
        ovs_vsctl(["set", "bridge", br, "protocols=OpenFlow13,OpenFlow15"])
        ovs_vsctl(["set-controller", br, "tcp:127.0.0.1:6633"])
        hypervisor = getHyhpervisor()
        server = '"unix:' + ovs_rundir + '/' + br + '.mgmt' + '"'
        return ["Chassis.put(Chassis{" + ", ".join([mkChassisId(hypervisor), "false", server, '""'])  + "})"]
    else:
        log("cocoon does not care about this bridge")
        return []

def ovsAddPort(cmd):
    br = getField(cmd, 'Bridge').children[0].value
    port = getField(cmd, 'Port').children[0].value
    entries = getList(getField(cmd, 'TableEntry_0'), 'TableEntry', 'TableEntry_0')
    log("add-port " + br + ' ' + port + ' ' + ' '.join(map(formatTableEntry, entries)))
    if br == "br-int":
        hypervisor = getHyhpervisor()
        pnum = None
        for e in entries:
            (col, key, vals) = getTableEntry(e)
            if col == "ofport-request":
                pnum = vals[0]
        if pnum == None:
            pnum = ovs_vsctl(["get", "Interface", port, "ofport"])
        return ["VSwitchPort.put(VSwitchPort{" + ", ".join([mkVPortId(port), '"' + port + '"', mkChassisId(hypervisor), pnum])  + "})"]
    else:
        log("cocoon does not care about this port")
        return []

def ovsSet(cmd):
    table = getField(cmd, 'Table').children[0].value
    record = getField(cmd, 'Record').children[0].value
    entries = getList(getField(cmd, 'TableEntry_1'), 'TableEntry', 'TableEntry_1')
    log("set " + table + ' ' + record + ' ' + ' '.join(map(formatTableEntry, entries)))
    cmds = []
    if table == "Interface":
        for e in entries:
            cmds += ovsSetInterface(record, e)
    elif table == "Open_vSwitch":
        for e in entries:
            cmds += ovsSetOVS(e)
    elif table == "bridge" and record == "br-int":
        for e in entries:
            cmds += ovsSetBridge(e)
    return cmds

def ovsSetInterface(iface, e):
    (col, key, vals) = getTableEntry(e)
    if col == "external-ids" and key == "iface-id":
        return ["LPortBinding.put(LPortBinding{" + mkLPortId(vals[0]) + ", " + mkVPortId(iface)  + "})"]
    else: 
        return []

def ovsSetOVS(e):
    (col, key, vals) = getTableEntry(e)
    if col == "external-ids" and key == "ovn-encap-ip":
        hypervisor = getHyhpervisor()
        ip = "32'h%x" % netaddr.IPAddress(vals[0])
        vxportname = hypervisor + "-vxlan"
        ovs_vsctl(["add-port", "br-int", vxportname, "--", "set", "interface", vxportname, "type=vxlan", "options:remote_ip=flow", "options:local_ip="+vals[0], "options:key=flow"])
        pnum = ovs_vsctl(["get", "Interface", vxportname, "ofport"])
        return ["TunnelPort.put(TunnelPort{" + ", ".join([mkTunPortId(hypervisor), pnum, mkChassisId(hypervisor), ip]) + "})"]
    else:
        return []

def ovsSetBridge(e):
    return []

ovsHandlers = { 'AddBr'     : ovsAddBr
              , 'AddPort'   : ovsAddPort
              , 'Set'       : ovsSet}

def testIpMatch():
    """
    Test regular expressions for matching IP addresses
    """
    mo = re.match(r'\d{1,3}[.]\d{1,3}[.]\d{1,3}[.]\d{1,3}', "192.168.1.5")
    assert(mo)
    ipv6address = "([0-9a-fA-F]{0,4}:){1,7}([0-9a-fA-F]{0,4})"
#     |
# ((25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])\.){3,3}
# (25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])|          # ::255.255.255.255   ::ffff:255.255.255.255  ::ffff:0:255.255.255.255  (IPv4-mapped IPv6 addresses and IPv4-translated addresses)
# ([0-9a-fA-F]{1,4}:){1,4}:
# ((25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])\.){3,3}
# (25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])           # 2001:db8:3:4::192.0.2.33  64:ff9b::192.0.2.33 (IPv4-Embedded IPv6 Address)
# )
# """
    ipv6tests = """
1:2:3:4:5:6:7:8
1::
1:2:3:4:5:6:7::
1::8
1:2:3:4:5:6::8
1:2:3:4:5:6::8
1::7:8
1:2:3:4:5::7:8
1:2:3:4:5::8
1::6:7:8
1:2:3:4::6:7:8
1:2:3:4::8
1::5:6:7:8
1:2:3::5:6:7:8
1:2:3::8
1::4:5:6:7:8
1:2::4:5:6:7:8
1:2::8
1::3:4:5:6:7:8
1::3:4:5:6:7:8
1::8
::2:3:4:5:6:7:8
::2:3:4:5:6:7:8
::8
::
fe80::ea2a:eaff:fe28:13
::255.255.255.255
::ffff:255.255.255.255
::ffff:0:255.255.255.255
2001:db8:3:4::192.0.2.33
64:ff9b::192.0.2.33
fe80::
"""
    for add in ipv6tests.split("\n"):
        if not add.strip():
            continue
        mo = re.match(ipv6address, add, re.X)
        assert mo, add

    regex = re.compile(ipv6address)
    mo = regex.match("fe80::ea2a:eaff:fe28:13/64 192.169.0.13", 0)
    assert mo
    assert mo.group(0) == "fe80::ea2a:eaff:fe28:13", mo.group(0)

ovnTestLines = """
ovn-nbctl --timeout=30 init
ovn-nbctl --timeout=30 ls-add lsw0
ovn-nbctl --timeout=30 lsp-add lsw0 lp11
ovn-nbctl --timeout=30 lsp-set-addresses lp11 'f0:00:00:00:00:11 192.168.0.11' unknown
ovn-nbctl --timeout=30 lsp-set-addresses lp11 f0:00:00:00:00:11 192.168.0.11 unknown
ovn-nbctl --timeout=30 lsp-add lsw0 lp12
ovn-nbctl --timeout=30 lsp-set-addresses lp12 'f0:00:00:00:00:12 192.168.0.12'
ovn-nbctl --timeout=30 lsp-set-port-security lp12 f0:00:00:00:00:12
ovn-nbctl --timeout=30 lsp-add lsw0 lp13
ovn-nbctl --timeout=30 lsp-set-addresses lp13 'f0:00:00:00:00:13 192.168.0.13 fe80::ea2a:eaff:fe28:13/64 192.169.0.13'
ovn-nbctl --timeout=30 lsp-set-port-security lp13 f0:00:00:00:00:13
ovn-nbctl --timeout=30 lsp-add lsw0 lp21
ovn-nbctl --timeout=30 lsp-set-addresses lp21 'f0:00:00:00:00:21 192.168.0.21' unknown
ovn-nbctl --timeout=30 lsp-add lsw0 lp22
ovn-nbctl --timeout=30 lsp-set-addresses lp22 'f0:00:00:00:00:22 192.168.0.22'
ovn-nbctl --timeout=30 lsp-set-port-security lp22 f0:00:00:00:00:22
ovn-nbctl --timeout=30 lsp-add lsw0 lp23
ovn-nbctl --timeout=30 lsp-set-addresses lp23 'f0:00:00:00:00:23 192.168.0.23 fe80::ea2a:eaff:fe28:23/64 192.169.0.23'
ovn-nbctl --timeout=30 lsp-set-port-security lp23 f0:00:00:00:00:23
ovn-nbctl --timeout=30 lsp-add lsw0 lp31
ovn-nbctl --timeout=30 lsp-set-addresses lp31 'f0:00:00:00:00:31 192.168.0.31' unknown
ovn-nbctl --timeout=30 lsp-add lsw0 lp32
ovn-nbctl --timeout=30 lsp-set-addresses lp32 'f0:00:00:00:00:32 192.168.0.32'
ovn-nbctl --timeout=30 lsp-set-port-security lp32 f0:00:00:00:00:32
ovn-nbctl --timeout=30 lsp-add lsw0 lp33
ovn-nbctl --timeout=30 lsp-set-addresses lp33 'f0:00:00:00:00:33 192.168.0.33 fe80::ea2a:eaff:fe28:33/64 192.169.0.33'
ovn-nbctl --timeout=30 lsp-set-port-security lp33 f0:00:00:00:00:33
ovn-nbctl --timeout=30 acl-add lsw0 from-lport 1000 'eth.type == 0x1234' drop
ovn-nbctl --timeout=30 acl-add lsw0 from-lport 1000 'eth.type == 0x1235 && inport == "lp11"' drop
ovn-nbctl --timeout=30 acl-add lsw0 to-lport 1000 'eth.type == 0x1236 && outport == "lp33"' drop
ovn-nbctl --timeout=30 create Address_Set name=set1 'addresses="f0:00:00:00:00:11","f0:00:00:00:00:21","f0:00:00:00:00:31"'
ovn-nbctl --timeout=30 acl-add lsw0 to-lport 1000 'eth.type == 0x1237 && eth.src == $set1 && outport == "lp33"' drop
ovn-nbctl --timeout=30 lsp-set-addresses lp13 'f0:00:00:00:00:13 192.168.0.13 invalid 192.169.0.13'
ovn-nbctl --timeout=30 lsp-add ls2 ln2 '' 101
ovn-nbctl lsp-add ls_name ln_port_name "" 101
"""

ovsTestLines = """
ovs-vsctl add-br n1
ovs-vsctl -- add-port n1 hv1_br-phys -- set Interface hv1_br-phys options:pstream=punix:/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv1_br-phys.sock options:rxq_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv1_br-phys-rx.pcap options:tx_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv1_br-phys-tx.pcap
ovs-vsctl -- add-port n1 hv2_br-phys -- set Interface hv2_br-phys options:pstream=punix:/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv2_br-phys.sock options:rxq_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv2_br-phys-rx.pcap options:tx_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv2_br-phys-tx.pcap
ovs-vsctl -- add-port n1 hv3_br-phys -- set Interface hv3_br-phys options:pstream=punix:/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv3_br-phys.sock options:rxq_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv3_br-phys-rx.pcap options:tx_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv3_br-phys-tx.pcap
ovs-vsctl --no-wait -- init
ovs-vsctl show
ovs-vsctl --timeout=30 add-br br-phys
ovs-vsctl --timeout=30 add-port br-int vif11 -- set Interface vif11 external-ids:iface-id=lp11 options:tx_pcap=hv1/vif11-tx.pcap options:rxq_pcap=hv1/vif11-rx.pcap ofport-request=11
ovs-vsctl --timeout=30 add-port br-int vif12 -- set Interface vif12 external-ids:iface-id=lp12 options:tx_pcap=hv1/vif12-tx.pcap options:rxq_pcap=hv1/vif12-rx.pcap ofport-request=12
ovs-vsctl --timeout=30 add-port br-int vif13 -- set Interface vif13 external-ids:iface-id=lp13 options:tx_pcap=hv1/vif13-tx.pcap options:rxq_pcap=hv1/vif13-rx.pcap ofport-request=13
ovs-vsctl --timeout=30 add-port br-int vif21 -- set Interface vif21 external-ids:iface-id=lp21 options:tx_pcap=hv2/vif21-tx.pcap options:rxq_pcap=hv2/vif21-rx.pcap ofport-request=21
ovs-vsctl --timeout=30 add-port br-int vif22 -- set Interface vif22 external-ids:iface-id=lp22 options:tx_pcap=hv2/vif22-tx.pcap options:rxq_pcap=hv2/vif22-rx.pcap ofport-request=22
ovs-vsctl --timeout=30 add-port br-int vif23 -- set Interface vif23 external-ids:iface-id=lp23 options:tx_pcap=hv2/vif23-tx.pcap options:rxq_pcap=hv2/vif23-rx.pcap ofport-request=23
ovs-vsctl --timeout=30 add-port br-int vif31 -- set Interface vif31 external-ids:iface-id=lp31 options:tx_pcap=hv3/vif31-tx.pcap options:rxq_pcap=hv3/vif31-rx.pcap ofport-request=31
ovs-vsctl --timeout=30 add-port br-int vif32 -- set Interface vif32 external-ids:iface-id=lp32 options:tx_pcap=hv3/vif32-tx.pcap options:rxq_pcap=hv3/vif32-rx.pcap ofport-request=32
ovs-vsctl --timeout=30 add-port br-int vif33 -- set Interface vif33 external-ids:iface-id=lp33 options:tx_pcap=hv3/vif33-tx.pcap options:rxq_pcap=hv3/vif33-rx.pcap ofport-request=33
ovs-vsctl --timeout=30 get Interface br-phys mac_in_use
ovs-vsctl --timeout=30 -- set Interface br-phys options:tx_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv1/br-phys-tx.pcap options:rxq_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv1/br-phys-rx.pcap -- add-port br-phys br-phys_n1 -- set Interface br-phys_n1 options:stream=unix:/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv1_br-phys.sock options:rxq_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv1/br-phys_n1-rx.pcap options:tx_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv1/br-phys_n1-tx.pcap
ovs-vsctl --timeout=30 -- set Interface br-phys options:tx_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv2/br-phys-tx.pcap options:rxq_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv2/br-phys-rx.pcap -- add-port br-phys br-phys_n1 -- set Interface br-phys_n1 options:stream=unix:/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv2_br-phys.sock options:rxq_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv2/br-phys_n1-rx.pcap options:tx_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv2/br-phys_n1-tx.pcap
ovs-vsctl --timeout=30 -- set Interface br-phys options:tx_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv3/br-phys-tx.pcap options:rxq_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv3/br-phys-rx.pcap -- add-port br-phys br-phys_n1 -- set Interface br-phys_n1 options:stream=unix:/home/mbudiu/git/ovs/tests/testsuite.dir/2317/main/hv3_br-phys.sock options:rxq_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv3/br-phys_n1-rx.pcap options:tx_pcap=/home/mbudiu/git/ovs/tests/testsuite.dir/2317/hv3/br-phys_n1-tx.pcap
ovs-vsctl --timeout=30 -- set Open_vSwitch . external-ids:system-id=hv1 -- set Open_vSwitch . external-ids:ovn-remote=unix:/home/mbudiu/git/ovs/tests/testsuite.dir/2317/ovn-sb/ovn-sb.sock -- set Open_vSwitch . external-ids:ovn-encap-type=geneve,vxlan -- set Open_vSwitch . external-ids:ovn-encap-ip=192.168.0.1 -- add-br br-int -- set bridge br-int fail-mode=secure other-config:disable-in-band=true
ovs-vsctl --timeout=30 -- set Open_vSwitch . external-ids:system-id=hv2 -- set Open_vSwitch . external-ids:ovn-remote=unix:/home/mbudiu/git/ovs/tests/testsuite.dir/2317/ovn-sb/ovn-sb.sock -- set Open_vSwitch . external-ids:ovn-encap-type=geneve,vxlan -- set Open_vSwitch . external-ids:ovn-encap-ip=192.168.0.2 -- add-br br-int -- set bridge br-int fail-mode=secure other-config:disable-in-band=true
ovs-vsctl --timeout=30 -- set Open_vSwitch . external-ids:system-id=hv3 -- set Open_vSwitch . external-ids:ovn-remote=unix:/home/mbudiu/git/ovs/tests/testsuite.dir/2317/ovn-sb/ovn-sb.sock -- set Open_vSwitch . external-ids:ovn-encap-type=geneve,vxlan -- set Open_vSwitch . external-ids:ovn-encap-ip=192.168.0.3 -- add-br br-int -- set bridge br-int fail-mode=secure other-config:disable-in-band=true

"""

def testStrings(str, parser):
    lines = str.split("\n")
    for line in lines:
        if not line.strip():
            continue
        # drop first word
        tail = " ".join(line.split()[1:])
        parseOptions(parser, tail)

def testIpConversion():
    bytes = convertIpToBytes('192.168.1.2')
    assert bytes == "c0a80102", bytes
    bytes = convertIpToBytes('2001:db8::1')
    assert bytes == "20010db8000000000000000000000001", bytes

def testStorage():
    storage = PersistentStore("./x")
    storage.clear()
    storage.set("c", "10")
    value = storage.get("c")
    assert value == "10", value
    storage.set("b", "20")
    value = storage.get("b")
    assert value == "20"
    storage.set("a", 10)
    value = storage.get("a")
    assert value == 10, value
    storage.set("b", [10, 20, 30])
    value = storage.get("b")
    assert value == [10, 20, 30], value
    storage.close()

    storage1 = PersistentStore("./x")
    value = storage1.get("a")
    assert value == 10, value
    value = storage1.get("b")
    assert value == [10, 20, 30], value
    value = storage1.get("c")
    assert value == "10", value
    storage1.close()

def test():
    testIpConversion()
    testIpMatch()
    testStorage()
    testStrings(ovnTestLines, getOvnParser())
    testStrings(ovsTestLines, getOvsParser())

if __name__ == "__main__":
    main()
