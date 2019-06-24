from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

import logging
import unittest

INS_INIT_UPDATE = 0x50
INS_EXT_AUTH    = 0x82
INS_BEGIN_RMAC  = 0x7A
INS_END_RMAC    = 0x78

# masks for "i" parameter
M_PSEUDO     = 0x10    # 1/0: Pseudo-random / random card challenge
M_RMAC       = 0x20    # R-MAC, no R-ENC
M_RMACENC    = 0x60    # both R-MAC and R-MAC
# mask for SL
SL_CMAC         = 0x01
SL_CENC         = 0x02
SL_RMAC         = 0x10
SL_RENC         = 0x20

class DDC(object):
    """ Data derivation constants. """
    CardCrypto    = 0x00
    HostCrypto    = 0x01
    CardChallenge = 0x02
    S_ENC         = 0x04
    S_MAC         = 0x06
    S_RMAC        = 0x07


def partition(alist, indices):
    """ Split alist at positions defined in indices. """
    indices = list(indices)
    return [alist[i:j] for i, j in zip([0]+indices, indices+[None])]

def logCh(CLA):
    """ Take log. channel from CLA byte """
    if CLA & 0x40:
        return 4 + CLA & 0x0F
    else:
        return CLA & 0x03

def CMAC(key, data):
    """ Calculate CMAC using AES as underlaying cipher.
    key     -  a key used for CMAC calculation (string 16, 24 or 32B long)
    data    - data to be signed (string)
    Returns CMAC as a string 16B long. """
    IrrPoly = 0x87     # irr. polynomial for F2m, m = 128
    BS = 16            # block size of AES

    def polyMulX(poly):
        """Interpret value as a polynomial over F2m and multiply by the
        polynomial x (modulo irreducible polynomial)"""
        # vals = list(unpack(">qq", poly))
        v0 = int.from_bytes(poly[:8], 'big', signed=True)
        v1 = int.from_bytes(poly[8:], 'big', signed=True)
        carry = v1 < 0 and 1 or 0
        v1 = ((v1 << 1) % 0x10000000000000000)
        if v0 < 0:
            v1 ^= IrrPoly
        v0 = ((v0 << 1) % 0x10000000000000000) + carry
        # return pack(">QQ", *vals)
        return v0.to_bytes(8, 'big') + v1.to_bytes(8, 'big')

    # kcv = AES.new(key, AES.MODE_ECB).encrypt(b'\x00'*BS)
    kcv = Cipher(algorithms.AES(key), modes.ECB(), default_backend()).encryptor().update(b'\x00'*BS)

    xorKey1 = polyMulX(kcv)
    xorKey2 = polyMulX(xorKey1)
    odata = list(data)
    sLB = len(data) % BS
    if(sLB > 0 or len(data) == 0):
        odata += [0x80] + [0]*(BS-sLB-1)
        xorkey = xorKey2
    else:
        xorkey = xorKey1
    for i in range(BS):
        odata[-BS+i] ^= xorkey[i]
    data = bytes(odata)

    # cipher = AES.new(key, AES.MODE_CBC, IV=b'\x00'*BS)
    # sig = cipher.encrypt(data)[-BS:]
    
    cipher = Cipher(algorithms.AES(key), modes.CBC(b'\x00'*BS), default_backend())
    sig = cipher.encryptor().update(data)

    return sig[-BS:]

def KDF(key, const, L, context):
    """ Key derivation scheme as defined in [GP AmD] 4.1.5
    key      - a key used for CMAC calculation (string 16, 24 or 32B long)
    const    - a constant from DDC (u8)
    L        - bit length of required output (u16)
    context  - a context entering calculation (string)
    Returns derived data as string L/8 bytes long."""
    nbl = (L + 127) // 128
    res = b''
    for i in range(1, nbl+1):
        data = b'\x00'*11 + const.to_bytes(1, 'big') + b'\x00' + L.to_bytes(2, 'big') + i.to_bytes(1, 'big') + context
        res += CMAC(key, data)
    BL = L // 8
    return res[:BL]

def pad80(bs, BS=8):
    """ Pad bytestring bs: add b'\x80' and b'\x00'*
        so the result to be multiple of BS."""
    l = BS - 1 - (len(bs) % BS)
    return bs + b'\x80' + b'\x00'*l

def unpad80(bs, BS=8):
    """ Remove 80 00* padding. Return unpadded bs.
        Raise AssertionError if padding is wrong. """
    for i in range(-1, -1 - BS, -1):
        # self.logger.debug(bs.hex())
        if bs[i] != 0x00:
            break
    assert bs[i] == 0x80, 'Wrong 80 00* padding, bs[%i] = %s vs. %s' % (i, bs[i], 0x80)

    return bs[:i]

class SCP03:
    """ Implementation of SCP03 calculation. """

    def __init__(self, **kw):
        """Constructor of SCP03 object.
        Expected parameters (in dict):
          i            - parameter of SCP03, (u8, default M_PSEUDO)
          SD_AID       - AID of security domain to authenticate to (string,
                         default bytes.fromhex('A000000151000000'))
          keyENC, keyMAC, keyDEK - static keys (strings 16, 24,  32B long)
          keyVer       - key version, (u8), default 0x30
          seqCounter   - sequence counter, (u24, default 0x000000)
          diverData    - bytes 1-10 of Init Update response (string 10B long,
                         default b'\x00'*10)
          verbose      - true or false for debug output
        """

        logging.basicConfig(format="%(levelname)s:%(filename)s:%(funcName)s:%(lineno)s:%(message)s")
        self.logger = logging.getLogger('SCP03')
        if kw.get('verbose', False):
            self.logger.setLevel(logging.DEBUG)

        i = kw.get('i', 0x70)  # default value
        i %= 0x100
        assert i & ~(M_PSEUDO | M_RMACENC) == 0, "RFU bits nonzero"
        assert i != M_RMACENC ^ M_RMAC, "RENC without RMAC"
        self.i = i

        self.SD_AID = kw.get('SD_AID', bytes.fromhex('A000000151000000'))
        assert 5 <= len(self.SD_AID) and len(self.SD_AID) <= 16, "Wrong AID length: %d" % len(self.SD_AID)

        for k in ('keyENC', 'keyMAC', 'keyDEK'):
            assert k in kw, "Mandatory key %s missing" % k
            assert len(kw[k]) in (16, 24, 32), "Wrong %s length: %d" % (k, len(kw[k]))
            self.__dict__[k] = kw[k]

        keyVer = kw.get('keyVer', 0x30)
        # assert 0x30 <= keyVer and keyVer <= 0x3F, \
        #     "Wrong key version %02X" % keyVer
        self.keyVer = keyVer

        seqCounter = kw.get('seqCounter', 0)
        assert 0 <= seqCounter and seqCounter < 0x1000000, "Wrong seq. counter value %X" % seqCounter
        self.seqCounter = seqCounter

        self.diverData = kw.get('diverData', b'\x00'*10)
        assert len(self.diverData) == 10, "Wrong length of diver. data: %d" % len(self.diverData)

    def initUpdate(self, host_challenge=b'\x00'*8, logCh=0):
        """ Return APDU for Initial Update (as list[u8]).
        Parameters:
            host_challenge (optional, default '0000000000000000')
            logCh - logical channel (optional, default 0)
         """
        assert 0 <= logCh and logCh < 20, "Wrong log. channel: %d" % logCh
        self.logCh = logCh
        assert len(host_challenge) == 8, "Wrong length of host challenge: %d" % len(host_challenge)
        self.host_challenge = host_challenge

        apdu = [self.CLA(False), INS_INIT_UPDATE, self.keyVer, 0, 8] + list(self.host_challenge)
        return apdu

    def initUpdateResp(self, card_challenge=None):
        """ Return expected response to Initial Update (as string).
          card_challenge - card challenge if i & M_PSEUDO == 0 """
        self.deriveKeys(card_challenge)
        resp = self.diverData + bytes([self.keyVer, 3, self.i]) + self.card_challenge + self.card_cryptogram
        if self.i & M_PSEUDO:
            resp += self.seqCounter.to_bytes(3, 'big')
        return resp

    def parseInitUpdate(self, apdu):
        """ Parse Init Update APDU (list[u8]) and if correct, set
        log. channel and host challenge from it. """
        cla = apdu[0]
        assert 0x80 <= cla <= 0x83 or 0xC0 <= cla < 0xCF, "Wrong CLA"
        assert apdu[1] == INS_INIT_UPDATE, "Wrong INS"
        assert apdu[2] == self.keyVer, "Key version changed"
        # ignore P2?
        assert apdu[4] == len(apdu) - 5 == 8, "Wrong Lc/data length"
        self.logCh = logCh(cla)
        self.logger.debug(self.logCh)
        self.host_challenge = bytes(apdu[5:])
        self.logger.debug(self.host_challenge.hex())

    def parseInitUpdateResp(self, resp):
        """ Parse response to Init Update and if correct set diverData,
        seqCounter, and card_challenge from it.
        resp     - response (list[u8])
        Raise exception in case of wrong response. """
        assert len(resp) in (29, 32), "Wrong length of response data to Init Update: %d" % len(resp)
        diverData, keyInfo, card_chal, card_cryptogram, seqCounter =partition(bytes(resp), (10, 13, 21, 29))
        kv, i = keyInfo[0], keyInfo[2]
        self.logger.debug('kv')
        self.logger.debug( hex(kv))
        self.logger.debug('self.kv')
        self.logger.debug( hex(self.keyVer))
        self.logger.debug('i')
        self.logger.debug( hex(i))
        self.logger.debug('self.i')
        self.logger.debug( hex(self.i))
        assert 0x30 <= kv and kv <= 0x3F, "Wrong key version in resp. to Init Update %02X" % kv
        assert keyInfo[1] == 0x03, "Wrong SCP number in resp. to Init Update %02X" % keyInfo[1]
        assert i & ~(M_PSEUDO | M_RMACENC) == 0 and i != M_RMACENC ^ M_RMAC, "Wrong SCP03 parameter %02X" % i

        self.logger.debug('diverData')
        self.logger.debug(diverData.hex())
        self.logger.debug('self.diverData')
        self.logger.debug(self.diverData.hex())
        self.i, self.keyVer, self.diverData = i, kv, diverData

        if self.i & M_PSEUDO:
            assert len(seqCounter) == 3, "Missing seq. counter"
            # self.seqCounter = s2int(seqCounter)
            seqCounter = int.from_bytes(seqCounter, 'big')

            self.logger.debug('self.seqCounter')
            self.logger.debug( hex(self.seqCounter))
            self.logger.debug('seqCounter')
            self.logger.debug( hex(seqCounter))
            self.seqCounter = seqCounter
        else:
            assert len(seqCounter) == 0, "Seq. counter shall not be present"

        self.deriveKeys(card_chal)
        self.logger.debug(card_cryptogram.hex())
        self.logger.debug(self.card_cryptogram.hex())
        assert card_cryptogram == self.card_cryptogram, "Recieved and calculated card cryptogram difer: %s vs. %s" % (card_cryptogram.hex(), self.card_cryptogram.hex())

    def extAuth(self, SL=1):
        """ Build and retrun Ext Auth APDU. """
        if SL & SL_RMAC:
            assert self.i & M_RMAC, "R-MAC not in SCP parameter"
        if SL & SL_RENC:
            assert self.i & M_RMACENC == M_RMACENC,     "R-ENC not in SCP parameter"
        assert SL in (0, SL_CMAC, SL_CMAC | SL_CENC, SL_CMAC | SL_RMAC,
                      SL_CMAC | SL_CENC | SL_RMAC,
                      SL_CMAC | SL_CENC | SL_RMAC | SL_RENC), "Wrong SL %02X" % SL
        self.SL = SL
        self.rmacSL = 0          # 0x10 or 0x30 after BEGIN R-MAC
        self.cmdCount = 0       # command counter for C-ENC ICV

        if 'host_cryptogram' not in self.__dict__:
            self.deriveKeys(None)

        data2sign = b'\x00'*16 + bytes([0x84, INS_EXT_AUTH, SL, 0, 0x10]) + self.host_cryptogram
        self.logger.debug('data2sign')
        self.logger.debug(data2sign.hex())
        
        self.MACchain = CMAC(self.SMAC, data2sign)
        self.logger.debug('self.MACchain')
        self.logger.debug(self.MACchain.hex())
        # apdu = [self.CLA(), INS_EXT_AUTH, SL, 0, 0x10] + [ord(x) for x in (self.host_cryptogram + self.MACchain[:8])]
        apdu = [self.CLA(), INS_EXT_AUTH, SL, 0, 0x10] + list(self.host_cryptogram + self.MACchain[:8])
        return apdu

    def parseExtAuth(self, apdu):
        """ Parse Ext Auth APDU (as hexstring) and
         check host cryptogram and MAC. """
        assert len(apdu) == 21, "Wrong data length"
        wapdu = self.extAuth(SL=apdu[2])
        assert apdu[:5] == wapdu[:5], "Wrong APDU header"
        assert apdu[5:13] == wapdu[5:13], "Wrong host cryptogram %s vs. %s" % (bytes(apdu[5:13]).hex(), bytes(wapdu[5:13]).hex())
        assert apdu[13:] == wapdu[13:], "Wrong MAC"
        self.SL = apdu[2]
        self.logger.debug('self.SL')
        self.logger.debug( self.SL)

    def beginRMAC(self, rmacSL, saltData=None):
        raise Exception('TODO')
        """ Build BEGIN R-MAC APDU (list[u8]).
        rmacSL - required SL, i.e. 0x10 for R-MAC and 0x30 for R-MAC and R-ENC
        saltData - data to be added to APDU (as #(saltData))
        Increase cmdCount."""
        # required rmacSL supported by SCP parameter
        if rmacSL & SL_RMAC:
            assert self.i & M_RMAC, "R-MAC not in SCP parameter"
        if rmacSL & SL_RENC:
            assert self.i & (M_RMACENC ^ M_RMAC), "R-ENC not in SCP parameter"
        # other bits must be zero
        assert rmacSL & ~(SL_RMAC | SL_RENC) == 0, "RFU bits nonzero"
        assert rmacSL & SL_RMAC != 0, "Wrong P1 for BEGIN R-MAC"
        assert self.SL & SL_RENC == 0, "R-ENC already in SL for BEGIN R-MAC"
        assert rmacSL > self.SL & SL_RMAC, "R-MAC already in SL for BEGIN R-MAC"
        assert self.SL & SL_CMAC, "C-MAC was not in Ext Auth"
        assert self.SL & SL_CENC or rmacSL & SL_RENC == 0

        if saltData is not None:
            assert len(saltData) < 255, "Too long data"
            data = chr(len(saltData)) + saltData
        else:
            data = ''
        apdu = [0x80, INS_BEGIN_RMAC, rmacSL, 1, len(data)] +    [ord(x) for x in data]
        wapdu = self.wrapAPDU(apdu)
        self.beginRmacSL = rmacSL
        return wapdu

    def deriveKeys(self, card_challenge=None):
        """ Derive session keys and calculate host_ and card_ cryptograms.
        card_challenge shall be present if i & M_PSEUDO == 0."""

        if 'host_challenge' not in self.__dict__:
            self.host_challenge = b'\x00'*8

        # card challenge calculation
        if self.i & M_PSEUDO:
            seqCounter = self.seqCounter.to_bytes(3, 'big')
            self.logger.debug('card_challenge')
            self.card_challenge = KDF(self.keyENC, DDC.CardChallenge, 0x0040, seqCounter + self.SD_AID)
            self.logger.debug(self.card_challenge.hex())
            if card_challenge is not None:
                assert card_challenge == self.card_challenge, "Provided and calculated card challenge difer: %s vs. %s" % (card_challenge.hex(), self.card_challenge.hex())
        else:
            assert len(card_challenge) == 8, "Wrong length of card challenge for randomly generated"
            self.card_challenge = card_challenge

        # session keys derivation
        context = self.host_challenge + self.card_challenge
        self.logger.debug('SENC')
        self.SENC = KDF(self.keyENC, DDC.S_ENC, 8*len(self.keyENC), context)
        self.logger.debug(self.SENC.hex())
        self.logger.debug('SMAC')
        self.SMAC = KDF(self.keyMAC, DDC.S_MAC, 8*len(self.keyMAC), context)
        self.logger.debug(self.SMAC.hex())
        self.logger.debug('SRMAC')
        self.SRMAC = KDF(self.keyMAC, DDC.S_RMAC, 8*len(self.keyMAC), context)
        self.logger.debug(self.SRMAC.hex())

        # cryptograms
        self.logger.debug('card_cryptogram')
        self.card_cryptogram = KDF(self.SMAC, DDC.CardCrypto, 0x0040, context)
        self.logger.debug(self.card_cryptogram.hex())
        self.logger.debug('host_cryptogram')
        self.host_cryptogram = KDF(self.SMAC, DDC.HostCrypto, 0x0040, context)
        self.logger.debug(self.host_cryptogram.hex())

        # reset MAC chaining value
        self.MACchain = None

    def CLA(self, zSecure=True, b8=0x80):
        """ Return CLA byte corresponding to logical channel, for
        secured/unsecured APDU.
        b8 - bit8 of CLA
         """
        if self.logCh < 4:
            return b8 + self.logCh + (zSecure and 0x04 or 0x00)
        else:
            return b8 + 0x40 + (self.logCh - 4) + (zSecure and 0x20 or 0x00)

    def closeSession():
        raise Exception('TODO')
        """ Clear all session data (session keys, logCh, challanges). """
        pass

    def checkAPDU(self, apdu):
        """ Check INS and Lc byte of APDU. Return Lc """
        if apdu[1] == 0xC0:
            assert len(apdu) == 5 and apdu[2:4] == [0, 0], 'Wrong Get response APDU'
        # else:
        #     assert apdu[1] & 0xF0 not in (0x60, 0x90), 'Wrong INS byte %02X' % apdu[1]
        lc = len(apdu) - 5
        assert len(apdu) >= 5, "Wrong APDU length: %d" % len(apdu)
        assert len(apdu) == 5 or apdu[4] == lc, "Lc differs from length of data: %d vs %d" % (apdu[4], lc)
        return lc

    def wrapAPDU(self, apdu):
        """ Wrap APDU for SCP03, i.e. calculate MAC and encrypt.
        Input APDU and output APDU are list of u8. """
        if type(apdu) != list:
            raise TypeError("Apdu must be list of bytes, not {}".format(type(apdu)))
        lc = self.checkAPDU(apdu)
        if apdu[1] == 0xC0:  # Get Response TPDU
            return apdu
        if 'beginRmaSL' in self.__dict__:
            self.rmacSL = self.beginRmacSL
            del self.beginRmacSL

        self.cmdCount += 1
        cla = apdu[0]
        b8 = cla & 0x80
        if (cla & 0x40 == 0 and cla & 0x03 > 0) or cla & 0x40 != 0:
            # check logical channels
            assert cla == self.CLA(False, b8), "CLA mismatch"
        scla = b8 | 0x04  # CLA without log. ch. but with secure messaging
        cdata = bytes(apdu[5:])

        if self.SL & SL_CENC and lc > 0:  # C-ENC
            # k = AES.new(self.SENC, AES.MODE_ECB)
            # ICV = k.encrypt(pack(">QQ", self.cmdCount / 0x10000000000000000,
            #                      self.cmdCount % 0x10000000000000000))

            ICV = Cipher(algorithms.AES(self.SENC), modes.ECB(), default_backend()).encryptor().update(
                self.cmdCount.to_bytes(16, 'big')
            )

            data2enc = pad80(cdata, 16)
            self.logger.debug('cmdCount')
            self.logger.debug(self.cmdCount)
            self.logger.debug('ICV')
            self.logger.debug(ICV.hex())
            self.logger.debug('data2enc')
            self.logger.debug(len(data2enc))
            self.logger.debug(data2enc.hex())

            # k = AES.new(self.SENC, AES.MODE_CBC, IV=ICV)
            # cdata = k.encrypt(data2enc)
            cdata = Cipher(algorithms.AES(self.SENC), modes.CBC(ICV), default_backend()).encryptor().update(data2enc)
            self.logger.debug(cdata.hex())
            lc = len(cdata)
            assert lc <= 0xFF, "Lc after encryption too long: %d" % lc

        if self.SL & SL_CMAC:    # C-MAC
            lc += 8
            assert lc <= 0xFF, "Lc after MACing too long: %d" % lc
            self.logger.debug('scla')
            self.logger.debug( scla)
            self.logger.debug('lc')
            self.logger.debug( lc)
            self.logger.debug('cdata')
            self.logger.debug( cdata)
            # data2sign = self.MACchain + chr(scla) + l2s(apdu[1:4]) + chr(lc) + cdata
            data2sign = self.MACchain + scla.to_bytes(1, 'big') + bytes(apdu[1:4]) + lc.to_bytes(1, 'big') + cdata
            self.logger.debug('data2sign')
            self.logger.debug(len(data2sign))
            self.logger.debug(data2sign.hex())
            self.MACchain = CMAC(self.SMAC, data2sign)
            cdata += self.MACchain[:8]

        apdu = [self.CLA(True, b8)] + apdu[1:4] + [lc] + list(cdata)
        self.logger.debug("[self.CLA(True, b8)]")
        self.logger.debug([self.CLA(True, b8)])
        self.logger.debug("apdu[1:4]")
        self.logger.debug(apdu[1:4])
        self.logger.debug("[lc]")
        self.logger.debug([lc])
        self.logger.debug("list(cdata)")
        self.logger.debug(list(cdata))
        return apdu

    def wrapResp(self, resp, sw1, sw2):
        """ Wrap expected response as card would do."""
        sw = (sw1 << 8) + sw2
        if not(sw == 0x9000 or sw1 in (0x62, 0x63)):
            assert len(resp) == 0, "No response data expected"
            return [], sw1, sw2
        dresp = bytes(resp)
        if (self.SL | self.rmacSL) & SL_RENC and len(dresp) > 0:
            # raise Exception('TODOD')
            assert len(dresp) <= 0xEF, "Data too long for RENC+RMAC"
            # k = AES.new(self.SENC, AES.MODE_ECB)
            # ICV = k.encrypt(pack(">QQ", 0x8000000000000000 |
            #                      self.cmdCount / 0x10000000000000000,
            #                      self.cmdCount % 0x10000000000000000))
            # k = AES.new(self.SENC, AES.MODE_CBC, IV=ICV)
            # dresp = k.encrypt(pad80(dresp, 16))

            ICV = Cipher(algorithms.AES(self.SENC), modes.ECB(), default_backend()).encryptor().update(
                (self.cmdCount | 0x8000000000000000).to_bytes(16, 'big')
            )
            dresp = Cipher(algorithms.AES(self.SENC), modes.CBC(ICV), default_backend()).encryptor().update(
                pad80(dresp, 16)
            )

        if (self.SL | self.rmacSL) & SL_RMAC:
            assert len(dresp) <= 0xF0, "Data too long for RMAC"
            # data2sign = self.MACchain + dresp + chr(sw1) + chr(sw2)
            data2sign = self.MACchain + dresp + sw1.to_bytes(1, 'big') + sw2.to_bytes(1, 'big')
            rmac = CMAC(self.SRMAC, data2sign)[:8]
            dresp += rmac
        self.logger.debug(resp)
        self.logger.debug(list(dresp))
        return list(dresp), sw1, sw2

    def unwrapAPDU(self, apdu, only_verify=False):
        # raise Exception('TODO')
        """ verify most recently MACed/encrypted APDU, decipher and check MAC. """
        lc = self.checkAPDU(apdu)
        if apdu[1] == 0xC0:  # Get Response TPDU
            return apdu
        if 'beginRmaSL' in self.__dict__:
            self.rmacSL = self.beginRmacSL
            del self.beginRmacSL

        if not only_verify:
            self.cmdCount += 1

        cla = apdu[0]
        b8 = cla & 0x80
        assert cla & 0x04, "Secure messaging missing"
        if (cla & 0x40 == 0 and cla & 0x03 > 0) or cla & 0x40 != 0:
            # check logical channels
            assert cla == self.CLA(True, b8), "CLA mismatch"
        scla = b8 | 0x04  # CLA without log. ch. but with secure messaging

        data = bytes(apdu[5:])

        self.logger.debug('data')
        self.logger.debug(len(data))
        self.logger.debug(data.hex())

        if self.SL & SL_CMAC:    # C-MAC
            assert lc >= 8, "Missing/ too short CMAC"
            sdata = data[:-8]
            # data2sign = self.MACchain + chr(scla) + l2s(apdu[1:4]) + chr(lc) + sdata
            data2sign = self.MACchain + scla.to_bytes(1, 'big') + bytes(apdu[1:4]) + lc.to_bytes(1, 'big') + sdata

            # self.MACchain = CMAC(self.SMAC, data2sign)
            next_MACchain = CMAC(self.SMAC, data2sign)
            self.logger.debug('next_MACchain[:8]')
            self.logger.debug(next_MACchain[:8].hex())
            self.logger.debug('next_MACchain[:8]')
            self.logger.debug(self.MACchain[:8].hex())
            self.logger.debug('data[-8:]')
            self.logger.debug(data[-8:].hex())
            if not only_verify:
                self.MACchain = next_MACchain
            assert data[-8:] == self.MACchain[:8], "Wrong CMAC, %s vs. %s" % (data[-8:].hex(), self.MACchain[:8].hex())
            data = sdata
            lc -= 8

        self.logger.debug(data.hex())

        if self.SL & SL_CENC and lc > 0:  # C-ENC
            # raise Exception('TODO')
            # assert lc % 16 == 0, "Encoded data length not multiple of BS"
            # k = AES.new(self.SENC, AES.MODE_ECB)
            # ICV = k.encrypt(pack(">QQ",
            #                      self.cmdCount / 0x10000000000000000,
            #                      self.cmdCount % 0x10000000000000000))
            # k = AES.new(self.SENC, AES.MODE_CBC, IV=ICV)
            # pdata = k.decrypt(data)
            # data = unpad80(pdata, 16)
            # assert len(data) > 0, "Empty data encrypted"
            # lc = len(data)

            assert lc % 16 == 0, "Encoded data length not multiple of BS"
            ICV = Cipher(algorithms.AES(self.SENC), modes.ECB(), default_backend()).encryptor().update(
                self.cmdCount.to_bytes(16, 'big')
            )
            self.logger.debug('cmdCount')
            self.logger.debug(self.cmdCount)
            self.logger.debug('ICV')
            self.logger.debug(ICV.hex())
            pdata = Cipher(algorithms.AES(self.SENC), modes.CBC(ICV), default_backend()).decryptor().update(data)
            self.logger.debug('pdata')
            self.logger.debug(pdata.hex())
            data = unpad80(pdata, 16)
            assert len(data) > 0, "Empty data encrypted"
            lc = len(data)

        apdu = [self.CLA(False, b8)] + apdu[1:4] + [lc] + list(data)
        return apdu

    def unwrapResp(self, resp, sw1, sw2):
        """ Unwrap response (decipher and check MAC)."""
        sw = (sw1 << 8) + sw2
        if not(sw == 0x9000 or sw1 in (0x62, 0x63)):
            assert len(resp) == 0, "No response data expected"
            return [], sw1, sw2

        dresp = list(resp)
        if (self.SL | self.rmacSL) & SL_RMAC:
            assert len(resp) >= 8, "Resp data shorter than 8: %d" % len(resp)
            # data2sign = self.MACchain + dresp[:-8] + chr(sw1) + chr(sw2)
            data2sign = self.MACchain + bytes(dresp[:-8]) + sw1.to_bytes(1, 'big') + sw2.to_bytes(1, 'big')
            rmac = CMAC(self.SRMAC, data2sign)[:8]
            assert list(rmac) == dresp[-8:], "Wrong R-MAC: %s vs expected: %s" % (bytes(dresp[-8:]).hex(), rmac.hex())
            dresp = dresp[:-8]

        if (self.SL | self.rmacSL) & SL_RENC and len(dresp) > 0:
            assert len(dresp) % 16 == 0, "Length of encrypted data not multiple of 16: %d" % len(dresp)

            # k = AES.new(self.SENC, AES.MODE_ECB)
            # ICV = k.encrypt(pack(">QQ", 0x8000000000000000 |
            #                      self.cmdCount / 0x10000000000000000,
            #                      self.cmdCount % 0x10000000000000000))
            # k = AES.new(self.SENC, AES.MODE_CBC, IV=ICV)
            # ddata = k.decrypt(dresp)

            ICV = Cipher(algorithms.AES(self.SENC), modes.ECB(), default_backend()).encryptor().update(
                (self.cmdCount | 0x8000000000000000).to_bytes(16, 'big')
            )
            ddata = Cipher(algorithms.AES(self.SENC), modes.CBC(ICV), default_backend()).decryptor().update(bytes(dresp))
            data = unpad80(ddata, 16)
            assert len(data) > 0, "Empty data encrypted"
        else:
            data = dresp
        return bytes(data), sw1, sw2

    def getDEK(self):
        return DEK(self.keyDEK)

class TestSettings(unittest.TestCase):

    def setUp(self):
        self.scp_par = {
        'SD_AID': bytes.fromhex('A000000018434D08090A0B0C000000'),
        'keyENC': b'@ABCDEFGHIJKLMNO',
        'keyMAC': bytes.fromhex('4011223344455667') + b'HIJKLMNO',
        'keyDEK': bytes.fromhex('9876543210') + b'@ABCDEFGHIJ',
        'keyVer': 0x30,
        'seqCounter': 0x00002A,
        'diverData': bytes.fromhex('000050C7606A8CF64810'),
        'verbose' : False, 
    }

    def sequence(self, level):
        scp03_host = SCP03(**self.scp_par)
        scp03_card = SCP03(**self.scp_par)

        # print('initUpdate')
        apdu = scp03_host.initUpdate()
        # print(bytes(apdu).hex())

        # print('parseInitUpdate')
        scp03_card.parseInitUpdate(apdu)

        # print('initUpdateResp')
        apdu = scp03_card.initUpdateResp()
        # print(bytes(apdu).hex())

        # print('parseInitUpdateResp')
        scp03_host.parseInitUpdateResp(apdu)

        # print('extAuth')
        apdu = scp03_host.extAuth(level)
        # print(apdu)

        # print('parseExtAuth')
        scp03_card.parseExtAuth(apdu)

        # print('wrapAPDU')
        apdu_host = list(bytes.fromhex('80 42 4140 05 1011121314'))
        # print(bytes(apdu_host).hex())
        wapdu = scp03_host.wrapAPDU(apdu_host)
        # print(bytes(wapdu).hex())
        
        # print('unwrapAPDU')
        apdu_card = scp03_card.unwrapAPDU(wapdu, only_verify=False)
        # print(bytes(apdu_card).hex())

        # print('wrapResp')
        resp_card = list(bytes.fromhex('DEADBEEF'))
        # print(bytes(resp_card).hex())
        wresp_card, sw1_card, sw2_card = scp03_card.wrapResp(resp_card, 0x90, 0x00)
        # print(bytes(wresp_card).hex(), bytes([sw1_card, sw2_card]).hex())

        # print('unwrapResp')
        resp_host, sw1_host, sw2_host = scp03_host.unwrapResp(wresp_card, sw1_card, sw2_card)
        # print(resp_host.hex())

        assert resp_host == bytes(resp_card), "response host (%s) != response card (%s)" % (resp_host.hex(), bytes(resp_card).hex())


    def test_SL_CMAC(self):
        level = SL_CMAC
        self.sequence(level)

    def test_SL_CMAC_SL_RMAC(self):
        level = SL_CMAC | SL_RMAC
        self.sequence(level)

    def test_SL_CMAC_SL_RMAC_SL_CENC(self):
        level = SL_CMAC | SL_RMAC | SL_CENC
        self.sequence(level)

    def test_SL_CMAC_SL_RMAC_SL_CENC_SL_RENC(self):
        level = SL_CMAC | SL_RMAC | SL_CENC | SL_RENC
        self.sequence(level)



if __name__ == '__main__':
    unittest.main()





