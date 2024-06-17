/**
 * PEM messages processing module source code. 
 * Log: 
 * 09/10/2002 - Kirill A. Lebedev - Initial revision.
 *
 * @name		PEM messages processing module source code (PemParser.c)
 * @version		$Revision: 58 $
 */
#include <Wpki.h>

#include "PemErr.h"
#include "PemParser.h"
#include "PemCompose.h"
#include "PemInternal.h"
#include <WpkiCtxHash.h>

#include <WpkiAsn1.h>
#include <pkcs1.h>
#include <WpkiUtils.h>
#include <WpkiCommonOID.h>

#include <Base64.h>
#include ".\..\..\pkcs\pkcs11\CryptokiKeys.h"

#include <stdio.h>
#include <stdlib.h>

//WpkiStatus
//TestSaveToFile(
//    IN WpkiPChar fileName,
//    IN WpkiPChar buff,
//    IN WpkiULong len
//)
//{
//    FILE* file;
//
//    if ( ((file  = fopen(fileName, "wb")) == NULL) ||
//         (fwrite(buff, 1, len, file) != len) ||
//         (fclose(file) != 0)
//       ) return WE_PEM_PARSER_ERROR;
//
//    return WE_PEM_SUCCESS;
//}

/* 
	max length for rsa sign used for decrypt rsa sign
	see rfc1423 "4.1.1  RSA Keys"
	"...
	For purposes of PEM, the modulus n may vary in size from 508 to 1024
	bits..."
*/
#define __MAX_RSA_KEY_LEN_IN_BYTE 128+MAX_LENGTH_OF_PADDING


#ifdef YYDEBUG
#include <stdio.h>
#endif

__WpkiPemLexerMode __statusNextMode = __PEM_DEFAULT_MODE;
__WpkiPemLexerMode __statusMode = __PEM_DEFAULT_MODE;

__WpkiPemToken __arrayPemTokens[WPKI_PEM_TOKENS_NUMBER] = 
{
	{"-----BEGIN PRIVACY-ENHANCED MESSAGE-----", BANNER_T},
	{"-----END PRIVACY-ENHANCED MESSAGE-----", TRAILER_T},
	{"Proc-Type", PRCTYPE_T},
	{"4", NUMBERT4_T},
	{"Content-Domain", CNTDMN_T},
	{"DEK-Info", DEKINFO_T},
	{"Originator-ID-Asymmetric", ORGIDAS_T},
	{"Originator-ID-Symmetric", ORGIDSM_T},
	{"Recipient-ID-Asymmetric", RCPIDAS_T},
	{"Recipient-ID-Symmetric", RCPIDSM_T},
	{"Originator-Certificate", ORGCERT_T},
	{"Issuer-Certificate", ISSCERT_T},
	{"MIC-Info", MICINFO_T},
	{"Key-Info", KEYINFO_T},
	{"CRL", CRL_T},
	{"ENCRYPTED", ENCRPTD_T},
	{"MIC-ONLY", MICONLY_T},
	{"MIC-CLEAR", MICCLR_T},
	{"RFC822", RFC822_T},
	{"DES-CBC", DESCBC_T},
	{"DES-EDE", DESEDE_T},
	{"DES-ECB", DESECB_T},
	{"RSA", RSA_T},
	{"RSA-MD2", RSAMD2_T},
	{"RSA-MD5", RSAMD5_T}
};


/**
 * This function extracts atom (RFC822) from buffer.
 * 
 *
 * @param    buffer,	[in] source message text
 * @param    token,		[inout] tiken for processing series of PEM messages
 */
WpkiSInt32 
__WpkiPemYyLex( 
			   WpkiPChar* in_ptr,
			   WpkiStatus *status,
			   YYSTYPE* yylval
			   ) 
{            

	YYSTYPE p = WPKI_NULL;
	WpkiUInt32 i = 0;
	WpkiUInt32 tokenToOut = 0;
	WpkiUInt32 lenToSkip = 0;
	WpkiUInt32 lenToken = 0;
	WpkiPChar str = *in_ptr;
	__WpkiPPemToken pToken = WPKI_NULL;
	PCONTEXT_INFO pContext = WPKI_NULL;

	p = __WpkiPemAalloc();
	
	/* if we can't alloc another terminal - return end-marker to make error in parser */
	if(p == WPKI_NULL)
	{
		*status = WE_PEM_NO_MEMORY;
		goto exit;
	}
	pContext = _GetContext();
	if(pContext->__isMessageEnd >= 2)
	{
		p->value  = str;
		/* end-marker = 0 */
		p->token  = 0;
		goto end;
	}

	/* skip linear whites-space char*/
	WPKI_PEM_SKIP_LWSC(str);
	if( *str == WPKI_PEM_DASH )
	{
		/* find TRAILER_T or BANNER_T token */
		if((pToken = __WpkiPemGetBANNER_TRAILER(str, &lenToSkip)) != WPKI_NULL)
		{
			/* return end-marker to finish parsing text */
			pContext->__isMessageEnd++;

			p->value  = str;
			p->token  = pToken->token;
			p->lenVal = __WpkiStrLen(pToken->identifier);
			goto end;
		}
	}

	if( !WPKI_PEM_IS_TEXT_MODE() )
	{
		/* find identifier */
		switch(*str)
		{
			case WPKI_PEM_COLON:
				{
					p->value  = str;
					p->lenVal = 1;
					p->token  = COLON_T;
					goto end;
				}
			case WPKI_PEM_COMMA:
				{
					p->value  = str;
					p->lenVal = 1;
					p->token  = COMMA_T;
					goto end;
				}
			case WPKI_PEM_CR:
				{
crlftoken:
					if( __WpkiPemIsContinueToken(str, &lenToSkip) )
					{
						/* if token contibue skip CRLF + LWSC */
						str += lenToSkip;
						break;
					}

					if( WPKI_PEM_IS_CRLF(str[0], str[1]) )
					{
						p->value  = str;
						p->lenVal = 2;
						p->token  = CRLF_T;
#ifdef YYDEBUG
						/* count line in buffer */
						pContext = _GetContext();
						(pContext->posInLine)++;
#endif /*YYDEBUG*/

						goto end;
					}
					else
					{
						*status = WE_PEM_PARSER_CRLF_WRONG;
						goto end;
					}
					break;
				}
		}/* end switch */
	}/* end if !WPKI_PEM_IS_TEXT_MODE() */
	else
	{
		/* if i skip linear whites-space char see line ~ 87 i MUST restore 
			pointer for that mode */
		str = *in_ptr;

		/* check for CRLF */
		if(*str ==WPKI_PEM_CR)
			goto crlftoken;
	}

	if( WPKI_PEM_IS_DEFAULT_MODE() )
	{
		/* identifier - field name */
		for ( i = 0 ; ((str[i] != 0) && __WpkiPemIsAtomChar(str[i])) ; i++)
			;
		
		/* find field name */
		if(i != 0 && ((pToken = __WpkiPemGetToken(str, i)) != WPKI_NULL) )
		{
			p->value  = str;
			p->token  = pToken->token;
			p->lenVal = i;
		}
		else 
		{
			if(__statusNextMode != __statusMode)
				__statusMode = __statusNextMode;

			__statusNextMode = __PEM_DEFAULT_MODE;
		}
	}
	if ( WPKI_PEM_IS_IACHAR_MODE() )
	{
		i = 0;
iachartoken:
		/* find identifier */
		for ( ; ((str[i] != 0) && __WpkiPemIsIaChar(str[i])) ; i++)
			;

		if( __WpkiPemIsContinueToken(&str[i], &lenToSkip) )
		{
			/* if token contibue skip CRLF + LWSC */
			i+= lenToSkip;
			goto iachartoken;
		}

		/* find sequence */
		if( i != 0 )
		{
			p->value  = str;
			p->token  = IACHARSEQ_T;
			p->lenVal = i;
		}
		else 
		{
			*status = WE_PEM_PARSER_IACHAR_WRONG;
			goto end;
		}
	}
	if ( WPKI_PEM_IS_HEX16_MODE() )
	{
		i = 0;
		lenToken = 0;
hex16token:
		/* find identifier */
		for ( ; ((str[i] != 0) && __WpkiPemIsHexChar( str[i] ) && (lenToken<WPKI_PEM_HEX16_TOKEN_LEN))  ; i++, lenToken++ )
			;

		/* find sequence */
		if( lenToken == WPKI_PEM_HEX16_TOKEN_LEN )
		{
			p->value  = str;
			p->token  = HEX16SEQ_T;
			p->lenVal = WPKI_PEM_HEX16_TOKEN_LEN;
		}
		else if( __WpkiPemIsContinueToken(&str[i], &lenToSkip) )
		{
			/* if token contibue skip CRLF + LWSC */
			i+= lenToSkip;
			goto hex16token;
		}
		else 
		{
			*status = WE_PEM_RARSER_HEX16_WRONG;
			goto end;
		}

	}
	if ( WPKI_PEM_IS_ENCBIN4_MODE() )
	{
		lenToken = 0;
		i = 0;
encbintoken:
		/* find identifier */
		for ( ; ((str[i] != 0) && __WpkiPemIsEncBinChar( str[i] ) && (lenToken<WPKI_PEM_ENCBIN4_TOKEN_LEN)); i++, lenToken++)
			;

		/* find sequence */
		if( lenToken == WPKI_PEM_ENCBIN4_TOKEN_LEN )
		{
			p->value  = str;
			p->token  = ENCBINGRP4_T;
			p->lenVal = WPKI_PEM_ENCBIN4_TOKEN_LEN;
		}
		else if( __WpkiPemIsContinueToken(&str[i], &lenToSkip) )
		{
			/* if token contibue skip CRLF + LWSC */
			i+= lenToSkip;
			goto encbintoken;
		}
		else 
		{
			*status = WE_PEM_PARSER_ENCBIN_WRONG;
			goto end;
		}
	}
	if ( WPKI_PEM_IS_TEXT_MODE() )
	{
		/* skip linear whites-space char*/
		/* _PEM_SKIP_LWSC(str);  - need ?????? */

		i = 0;
texttoken:
/*
	from RFC822
     text        =  <any CHAR, including bare    ; => atoms, specials,
                     CR & bare LF, but NOT       ;  comments and
                     including CRLF>             ;  quoted-strings are
                                                 ;  NOT recognized.
*/
		/* find identifier */
//		for ( ; ((str[i] != 0) && __WpkiPemIsTextChar( str[i], str[i+1] )) ; i++)
		for ( ; __WpkiPemIsTextChar( str[i], str[i+1] ) ; i++)
			;

		if( __WpkiPemIsContinueToken(&str[i], &lenToSkip) )
		{
			/* if token contibue skip CRLF + LWSC */
			i+= lenToSkip;
			goto texttoken;
		}

		/* find sequence */
		if( i > 0  )
		{
			p->value  = str;
			p->token  = TEXT_T;
			p->lenVal = i;
		}
		else 
		{
			*status = WE_PEM_PARSER_TEXT_WRONG;
			goto end;
		}
	}

end:
	/* new position after find identifier */
	*in_ptr = str + p->lenVal;

	/* remember token & pos in buffer in context for debug info */
	*yylval = p;

	tokenToOut = p->token;

#ifdef YYDEBUG
	pContext = _GetContext();
//	pContext->currentPosInBuffer = p->value;
	pContext->bufferLength       = p->lenVal;
	pContext->token              = p->token;
#endif /*YYDEBUG*/
exit:

	return ( tokenToOut );
}

WpkiStatus
__WpkiPemParserCaseProc1(
					 YYSTYPE p1, 
					 YYSTYPE p2
					 )
{
	WpkiPemPASymSeq tmp;
	WpkiStatus status;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc1()\n");
	/* error */
	if((p1->choice != __ORIGFLDSEQ) || ((p2 != WPKI_NULL) && (p2->choice != __RECEPFLDSEQ)))
	{
		yyerror("\n error: __WpkiPemParserCaseProc1 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif
	/* make WpkiPemPASymSeq object */
	if( (status = WpkiPemASymSeqConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc1 \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	tmp->origFlds  = p1->un.pOrigFldSeq;
	tmp->recepFlds = (p2 != WPKI_NULL ? p2->un.pRecepFldSeq : WPKI_NULL);

	p1->choice   = __ASYMSEQ;
	p1->un.pASymSeq = tmp;

	if(p2 != WPKI_NULL)
	{
		p2->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(p2);
	}

	return ( WE_PEM_SUCCESS );
}

WpkiStatus
__WpkiPemParserCaseProc2(
					 YYSTYPE p1, 
					 YYSTYPE p2,
					 YYSTYPE p3
					 )
{
	WpkiPemPSymSeq tmp;
	WpkiPemPSymSeq tmp1;
	WpkiStatus status;


#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc2()\n");
	/* error */
	if(((p1 != WPKI_NULL) && (p1->choice != __SYMSEQ)) || (p2->choice != __ORIGFLD) || ((p3 != WPKI_NULL)&&(p3->choice != __RECEPFLDSEQ)))
	{
		yyerror("\n error: __WpkiPemParserCaseProc2 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif
	/* make WpkiPemSymSeq object */
	if( (status = WpkiPemSymSeqConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc2 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	tmp->origFlds  = p2->un.pOrigFld;
	tmp->recepFlds = (p3 != WPKI_NULL ? p3->un.pRecepFldSeq : WPKI_NULL);

	if(p3 != WPKI_NULL)
	{
		p3->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(p3);
	}

	if(p1 != WPKI_NULL)
	{
		for(tmp1 = p1->un.pSymSeq; tmp1->next != WPKI_NULL; tmp1 = tmp1->next )
			;
		
		tmp1->next = tmp;

		p2->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(p2);
	}
	else
	{
		p2->choice = __SYMSEQ;
		p2->un.pSymSeq= tmp;
	}
	
	return ( WE_PEM_SUCCESS );
}

WpkiStatus
__WpkiPemParserCaseProc3(
					 YYSTYPE p1, 
					 YYSTYPE p2
					 )
{
	WpkiPemPSeqOfOrigFlds tmp;
	WpkiPemPSeqOfOrigFlds tmp1;
	WpkiStatus status;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc3()\n");
	/* error */
	if(((p1 != WPKI_NULL) && (p1->choice != __ORIGFLDSEQ)) || (p2->choice != __ORIGFLD))
	{
		yyerror("\n error: __WpkiPemParserCaseProc3 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiPemSymSeq object */
	if( (status = WpkiPemSeqOfOrFldConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc3 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	tmp->origField = p2->un.pOrigFld;

	if(p1 != WPKI_NULL)
	{
		for(tmp1 = p1->un.pOrigFldSeq; tmp1->next != WPKI_NULL; tmp1 = tmp1->next )
			;
		
		tmp1->next = tmp;

		p2->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(p2);
	}
	else
	{
		p2->choice      = __ORIGFLDSEQ;
		p2->un.pOrigFldSeq = tmp;
	}

	return ( WE_PEM_SUCCESS );
}

WpkiStatus
__WpkiPemParserCaseProc4(
					 YYSTYPE p1, 
					 YYSTYPE p2
					 )
{
	WpkiPemPSeqOfRecepFlds tmp;
	WpkiPemPSeqOfRecepFlds tmp1;
	WpkiStatus status;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc4()\n");
	/* error */
	if(((p1!=WPKI_NULL) && (p1->choice != __RECEPFLDSEQ)) || (p2->choice != __RECEPFLD))
	{
		yyerror("\n error: __WpkiPemParserCaseProc4 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiPemSymSeq object */
	if( (status = WpkiPemSeqOfRecFldConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc4 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	tmp->recipField = p2->un.pRecepFld;

	if(p1!=WPKI_NULL)
	{
		for(tmp1 = p1->un.pRecepFldSeq; tmp1->next != WPKI_NULL; tmp1 = tmp1->next )
			;
		
		tmp1->next = tmp;

		p2->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(p2);
	}
	else
	{
		p2->choice = __RECEPFLDSEQ;
		p2->un.pRecepFldSeq = tmp;
	}

	return ( WE_PEM_SUCCESS );
}

WpkiStatus
__WpkiPemParserCaseProc8(
					 YYSTYPE p1,
					 YYSTYPE p2
					 )
{
	WpkiPemPCrlSeq tmp;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc8()\n");
	/* error */
	if((p1->choice != __CRLSEQ) && (p2->choice != __CRLSEQ))
	{
		yyerror("\n error: __WpkiPemParserCaseProc8 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	for(tmp = p1->un.pCrlSeq; tmp->next != WPKI_NULL; tmp = tmp->next )
		;

	tmp->next = p2->un.pCrlSeq;

	p2->choice = __END_PEM_TOKEN_CHOICE;
	__WpkiPemAfree(p2);

	return ( WE_PEM_SUCCESS );
}

WpkiStatus
__WpkiPemParserCaseProc9(
					 YYSTYPE crl,
					 YYSTYPE cert,
					 YYSTYPE isscert
					 )
{
	WpkiStatus status;
	WpkiPemPCrlSeq tmp;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc9()\n");
	/* error */
	if(( crl->choice != __CRL ) || ((cert != WPKI_NULL) && (cert->choice != __CERT)) || ((isscert != WPKI_NULL) && (isscert->choice != __ISSUECERT)))
	{
		yyerror("\n error: __WpkiPemParserCaseProc9 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiPemSymSeq object */
	if( (status = WpkiPemCrlSeqConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc9 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	tmp->crl        = crl->un.crl;
	tmp->cert       = (cert != WPKI_NULL ? cert->un.cert : WPKI_NULL);
	tmp->issuercert = (isscert != WPKI_NULL ? isscert->un.issuercert : WPKI_NULL);

	crl->choice = __CRLSEQ;
	crl->un.pCrlSeq = tmp;

	if(cert != WPKI_NULL)
	{
		cert->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(cert);
	}

	if(isscert != WPKI_NULL)
	{
		isscert->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(isscert);
	}

	return ( WE_PEM_SUCCESS );
}

WpkiStatus
__WpkiPemParserCaseProc10(
					 YYSTYPE isscertSeq,
					 YYSTYPE isscert
					 )
{
	WpkiX509SeqOfCertificate* tmp = WPKI_NULL;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc10()\n");
	/* error */
	if(((isscertSeq != WPKI_NULL) && ( isscertSeq->choice != __ISSUECERT)) || (isscert->choice != __ISSUECERT))
	{
		yyerror("\n error: __WpkiPemParserCaseProc10 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif


	if(isscertSeq != WPKI_NULL)
	{
		for(tmp = isscertSeq->un.issuercert; tmp->next != WPKI_NULL; tmp = tmp->next )
			;

		tmp->next = tmp;
		isscert->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(isscert);
	}

	return ( WE_PEM_SUCCESS );
}

WpkiStatus
__WpkiPemParserCaseProc11(
					 YYSTYPE orgfld,
					 YYSTYPE keyinfo,
					 YYSTYPE issuercert_seq,
					 YYSTYPE micinfo
					 )
{
	WpkiPemPOrigFlds tmp;
	WpkiStatus status = WE_SUCCESS;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc11()\n");
	/* error */
	if((orgfld == WPKI_NULL)  || ((keyinfo != WPKI_NULL) && (keyinfo->choice != __KEYINFO)) || 
		((issuercert_seq != WPKI_NULL) && (issuercert_seq->choice != __ISSUECERT)) ||
		((micinfo != WPKI_NULL ) && (micinfo->choice != __MICINFO)) )
	{
		yyerror("\n error: __WpkiPemParserCaseProc11 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiPemOrigFlds object */
	if( (status = WpkiPemOrigFldsConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc11 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	switch(orgfld->choice)
	{
	case __CERT:
		{
			tmp->choice = WPKI_PEM_CERTID;
			tmp->un.cert   = orgfld->un.cert;
			break;
		}
	case __ASYMMID:
		{
			tmp->choice   = WPKI_PEM_ASYMID;
			tmp->un.origASym = orgfld->un.pASymmId;
			break;
		}
	case __SYMMID:
		{
			tmp->choice   = WPKI_PEM_SYMID;
			tmp->un.origSym = orgfld->un.pSymmId;
			break;
		}
	default:
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc11 \n");
#endif
		status = WE_PEM_PARSER_ERROR;
	};/* end switch */

	tmp->keyInfo    = (keyinfo != WPKI_NULL ? keyinfo->un.pKeyInfo : WPKI_NULL);
	tmp->issuercert = (issuercert_seq != WPKI_NULL ? issuercert_seq->un.issuercert : WPKI_NULL);
	tmp->micInfo    = (micinfo != WPKI_NULL ? micinfo->un.pMicInfo : WPKI_NULL);

	if(keyinfo != WPKI_NULL)
	{
		keyinfo->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(keyinfo);
	}

	if(issuercert_seq != WPKI_NULL)
	{
		issuercert_seq->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(issuercert_seq);
	}

	if(micinfo != WPKI_NULL)
	{
		micinfo->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(micinfo);
	}

	if(status != WE_SUCCESS)
	{
		WpkiPemOrigFldsDestroy(tmp);
		tmp = WPKI_NULL;
	}
	orgfld->choice   = __ORIGFLD;
	orgfld->un.pOrigFld = tmp;

	return ( status );
}

WpkiStatus
__WpkiPemParserCaseProc12(
					 YYSTYPE recfld,
					 YYSTYPE keyinfo
					 )
{
	WpkiPemPRecepFlds tmp;
	WpkiStatus status = WE_SUCCESS;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc12()\n");
	/* error */
	if( (recfld == WPKI_NULL)  || (keyinfo == WPKI_NULL) || ((keyinfo != WPKI_NULL) && (keyinfo->choice != __KEYINFO)) )
	{
		yyerror("\n error: __WpkiPemParserCaseProc12 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiPemRecepFlds object */
	if( (status = WpkiPemRecepFldsConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc12 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	switch(recfld->choice)
	{
	case __ASYMMID:
		{
			tmp->choice   = WPKI_PEM_ASYMID;
			tmp->un.recipASym = recfld->un.pASymmId;
			break;
		}
	case __SYMMID:
		{
			tmp->choice   = WPKI_PEM_SYMID;
			tmp->un.recipSym = recfld->un.pSymmId;
			break;
		}
	default:
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc12 \n");
#endif
		status = WE_PEM_PARSER_ERROR;
	};/* end switch */

	tmp->keyInfo    = (keyinfo != WPKI_NULL ? keyinfo->un.pKeyInfo : WPKI_NULL);

	if(keyinfo != WPKI_NULL)
	{
		keyinfo->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(keyinfo);
	}

	if(status != WE_SUCCESS)
	{
		WpkiPemRecepFldsDestroy(tmp);
		tmp = WPKI_NULL;
	}

	recfld->choice    = __RECEPFLD;
	recfld->un.pRecepFld = tmp;

	return ( status );

}


WpkiStatus
__WpkiPemParserCaseProc13(
					 YYSTYPE entid,
					 YYSTYPE issueau,
					 YYSTYPE ver
					 )
{
	WpkiPemPSymId tmp;
	WpkiStatus status = WE_SUCCESS;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc13()\n");
	/* error */
	if (entid == WPKI_NULL) 
	{
		yyerror("\n error: __WpkiPemParserCaseProc13 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiPemSymId object */
	if( (status = WpkiPemSymIdConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc13 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	/* don't need Decode from BASE 64 
	   alloc memory for fields
	*/
	if((status = WPKI_PEM_ALLOC((&tmp->entityId), entid->lenVal))!=WE_PEM_SUCCESS)
	{
		status = WE_PEM_NO_MEMORY;
		goto end;
	}
	WPKI_MEMCPY(tmp->entityId, entid->value, entid->lenVal);
	tmp->sizeEntId = entid->lenVal;

	if(issueau != WPKI_NULL)
	{
		if((status = WPKI_PEM_ALLOC((&tmp->iaId), issueau->lenVal))!=WE_PEM_SUCCESS)
		{
			status = WE_PEM_NO_MEMORY;
			goto end;
		}
		WPKI_MEMCPY(tmp->iaId, issueau->value, issueau->lenVal);
		tmp->sizeIaId = issueau->lenVal;
	}

	if(ver != WPKI_NULL)
	{
		if((status = WPKI_PEM_ALLOC((&tmp->versionId), ver->lenVal))!=WE_PEM_SUCCESS)
		{
			status = WE_PEM_NO_MEMORY;
			goto end;
		}
		WPKI_MEMCPY(tmp->versionId, ver->value, ver->lenVal);
		tmp->sizeVerId = ver->lenVal;
	}

end:
	if(status != WE_SUCCESS)
	{
		WpkiPemSymIdDestroy( tmp );
		tmp = WPKI_NULL;
	}

	entid->choice  = __SYMMID;
	entid->un.pSymmId = tmp;

	if(issueau != WPKI_NULL)
	{
		issueau->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(issueau);
	}

	if(ver != WPKI_NULL)
	{
		ver->choice = __END_PEM_TOKEN_CHOICE;
		__WpkiPemAfree(ver);
	}

	return ( status );
}

WpkiStatus
__WpkiPemParserCaseProc14(
					 YYSTYPE iaid,
					 YYSTYPE ver
					 )
{
	WpkiPemPASymId tmp;
	WpkiX509RdnSequence*  pRndSeq;
	WpkiStatus status = WE_SUCCESS;

	WpkiUInt32 len = 0;
	WpkiUInt32 realLen = 0;
	WpkiAsn1Octet *buffer = WPKI_NULL;
    WpkiAsn1Length bufferLen = 0;
    WpkiAsn1Status asnStatus;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc14()\n");
	/* error */
	if ((iaid == WPKI_NULL) || (ver == WPKI_NULL))
	{
		yyerror("\n error: __WpkiPemParserCaseProc14 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiPemSymId object */
	if( (status = WpkiPemASymIdConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc14 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	len = __WpkiPemParserSeqLen(iaid, &realLen, WPKI_TRUE);
	/* Decode from BASE 64 (alloc memory) */
	if((status = _Base64Decode(iaid->value, realLen, &buffer, &bufferLen ))==WE_SUCCESS)
	{
		/* Decode from DER to WpkiX509RdnSequence */
		if((asnStatus = WpkiAsn1BerDecode(
									&pRndSeq, 
									&TYPE(WpkiX509RdnSequence), 
									buffer, 
									bufferLen)) == WPKI_ASN1_SUCCESS)
		{
			tmp->iaId      = pRndSeq;
		}
		else
		{
			/* NOTE: it is currently decided who must free the memory if the decoding has failed */
			WPKI_PEM_FREE(tmp);
			tmp = WPKI_NULL;
			status = WE_PEM_ASN1DECODE_ERR;
		}
		
		PEM_CLEANUP(buffer);
	}
	else
		status =  WE_PEM_BASE64DECODE_ERR;
 
	if(status == WE_SUCCESS)
	{
		len = __WpkiPemParserSeqLen(ver, &realLen, WPKI_TRUE);
		tmp->versionId.length = realLen/2;
		
		status = WPKI_PEM_ALLOC(&(tmp->versionId.data), tmp->versionId.length);
		if(status == WE_SUCCESS)
		{
			status = __WpkiPemHexDecimalToHex(
					ver->value, 
					realLen, 
					tmp->versionId.data, 
					tmp->versionId.length);
		}
		else
			status = WE_PEM_NO_MEMORY;

	}

	if(status != WE_SUCCESS)
	{
		WpkiPemASymIdDestroy(tmp);
		tmp = WPKI_NULL;
	}

	iaid->choice    = __ASYMMID;
	iaid->un.pASymmId = tmp;

	ver->choice = __END_PEM_TOKEN_CHOICE;
	__WpkiPemAfree(ver);

	return ( status );
}

WpkiStatus
__WpkiPemParserCaseProc15(
					 YYSTYPE encbin
					 )
{
	WpkiX509Certificate* tmp;
	WpkiStatus status = WE_PEM_SUCCESS;
	WpkiUInt32 len = 0;
	WpkiUInt32 realLen = 0;

	WpkiAsn1Octet *buffer;
    WpkiAsn1Length bufferLen;
    WpkiAsn1Status asnStatus;


#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc15()\n");
	/* error */
	if (encbin == WPKI_NULL) 
	{
		yyerror("\n error: __WpkiPemParserCaseProc15 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiX509Certificate object from encbin */
	if((status = WPKI_PEM_ALLOC(&tmp, sizeof(WpkiX509Certificate)))!=WE_SUCCESS)
		return( WE_PEM_NO_MEMORY );
    
	len = __WpkiPemParserSeqLen(encbin, &realLen, WPKI_TRUE);
	/* Decode from BASE 64 (alloc memory) */
	if((status = _Base64Decode(encbin->value, realLen, &buffer, &bufferLen ))!=WE_SUCCESS)
		return( WE_PEM_BASE64DECODE_ERR );

	/* Decode from DER to WpkiX509Certificate */
	if((asnStatus = WpkiAsn1BerDecode(tmp, &TYPE(WpkiX509Certificate), buffer, bufferLen)) != WPKI_ASN1_SUCCESS)
    {
        /* NOTE: it is currently decided who must free the memory if the decoding has failed */
		WPKI_PEM_FREE(tmp);
		tmp = WPKI_NULL;
		status = WE_PEM_ASN1DECODE_ERR;
    }
	/* ToDo: verify */
	encbin->un.cert   = tmp;
	encbin->choice = __CERT;

	PEM_CLEANUP(buffer);

	return ( status );
}

WpkiStatus
__WpkiPemParserCaseProc16(
					 YYSTYPE encbin
					 )
{
	WpkiX509SeqOfCertificate* tmp;
	WpkiStatus status = WE_PEM_SUCCESS;
	WpkiUInt32 len = 0;
	WpkiUInt32 realLen = 0;

	WpkiAsn1Octet *buffer;
    WpkiAsn1Length bufferLen;
    WpkiAsn1Status asnStatus;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc16()\n");
	/* error */
	if (encbin == WPKI_NULL) 
	{
		yyerror("\n error: __WpkiPemParserCaseProc16 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiX509SeqOfCertificate object from encbin */
	if((status = WPKI_PEM_ALLOC(&tmp, sizeof(WpkiX509SeqOfCertificate)))!=WE_SUCCESS)
		return( WE_PEM_NO_MEMORY );

	tmp->next = WPKI_NULL;

	len = __WpkiPemParserSeqLen(encbin, &realLen, WPKI_TRUE);
	/* Decode from BASE 64 (alloc memory) */
	if((status = _Base64Decode(encbin->value, realLen, &buffer, &bufferLen ))!= WE_SUCCESS)
		return( WE_PEM_BASE64DECODE_ERR );

	/* Decode from DER to WpkiX509Certificate */
	if((asnStatus = WpkiAsn1BerDecode(&(tmp->data), &TYPE(WpkiX509Certificate), buffer, bufferLen)) != WPKI_ASN1_SUCCESS)
    {
        /* NOTE: it is currently decided who must free the memory if the decoding has failed */
		WPKI_PEM_FREE(tmp);
		tmp = WPKI_NULL;
		status = WE_PEM_ASN1DECODE_ERR;
    }
	/* ToDo: verify - for future */
	encbin->un.issuercert = tmp;
	encbin->choice     = __ISSUECERT;

	PEM_CLEANUP(buffer);

	return ( status );
}

WpkiStatus
__WpkiPemParserCaseProc17(
					 YYSTYPE micalgid,
					 YYSTYPE ikalgid,
					 YYSTYPE asymsignmic
					 )
{
	WpkiPemPMicInfo tmp;
	WpkiStatus status = WE_SUCCESS;
	WpkiUInt32 len = 0;
	WpkiUInt32 realLen = 0;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc17()\n");
	/* error */
	if ((micalgid == WPKI_NULL) || (ikalgid == WPKI_NULL) || (asymsignmic == WPKI_NULL))
	{
		yyerror("\n error: __WpkiPemParserCaseProc17 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiPemSymId object */
	if( (status = WpkiPemMicInfoConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc17 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	tmp->micAlgId = __WpkiPemParserGetMicAlgId(micalgid);
	tmp->ikAlgId  = __WpkiPemParserGetIkAlgId(ikalgid);

	/* Decode from BASE 64 (alloc memory) */
	len = __WpkiPemParserSeqLen(asymsignmic, &realLen, WPKI_TRUE);
	if((status = _Base64Decode(asymsignmic->value, realLen, &(tmp->micAsymSign), &(tmp->sizeSign) ))!=WE_SUCCESS)
		status = WE_PEM_BASE64DECODE_ERR;

	if(status != WE_SUCCESS)
	{
		WpkiPemMicInfoDestroy(tmp);
		tmp = WPKI_NULL;
	}
	
	micalgid->choice   = __MICINFO;
	micalgid->un.pMicInfo = tmp;

	__WpkiPemAfree(ikalgid);
	__WpkiPemAfree(asymsignmic);

	return ( status );
}

WpkiStatus
__WpkiPemParserCaseProc18(
					 YYSTYPE micalgid,
					 YYSTYPE symencdek,
					 YYSTYPE symencmic,
					 WpkiBool isKeyAssym
					 )
{
	WpkiPemPKeyInfo tmp;
	WpkiStatus status = WE_SUCCESS;
	WpkiUInt32 len = 0;
	WpkiUInt32 realLen = 0;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc18()\n");
	/* error */
	if ( (!isKeyAssym) && ( (micalgid == WPKI_NULL) || (symencdek == WPKI_NULL) || (symencmic == WPKI_NULL)) )
	{
		yyerror("\n error: __WpkiPemParserCaseProc18 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
	if ( (isKeyAssym) && (micalgid == WPKI_NULL) )
	{
		yyerror("\n error: __WpkiPemParserCaseProc18 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiPemSymId object */
	if( (status = WpkiPemKeyInfoConstruct( &tmp ))!= WE_SUCCESS)
	{
#ifdef YYDEBUG
		yyerror("\n error: __WpkiPemParserCaseProc18 (no memory) \n");
#endif
		return ( WE_PEM_NO_MEMORY );
	}

	if(isKeyAssym)
	{
	/* asymmetric key */
		tmp->isKeyAsymmetric = WPKI_TRUE;
		tmp->un.asymInfo.keyData = WPKI_NULL;
		/* Decode - BASE64 micalgid - its encbin sequences */
		len = __WpkiPemParserSeqLen(micalgid, &realLen, WPKI_TRUE);
		status = _Base64Decode(micalgid->value, realLen, 
			&(tmp->un.asymInfo.keyData), &(tmp->un.asymInfo.sizeKeyData) );
	}
	else
	{
	/* symmetric case */
		tmp->isKeyAsymmetric   = WPKI_FALSE;
		tmp->un.symInfo.micAlgId = __WpkiPemParserGetMicAlgId(micalgid);

		/* symencdek->value is string of ASCII hexadecimal digits */
		__WpkiPemHexDecimalToHex(
			symencdek->value, PEM_SYMENCDEK_SIZE,
			tmp->un.symInfo.decData, PEM_SYMENCDEK_SIZE);
		/* symencmic->value is string of ASCII hexadecimal digits */
		__WpkiPemHexDecimalToHex(
			symencmic->value, PEM_SYMENCMIC_SIZE,
			tmp->un.symInfo.micData, PEM_SYMENCMIC_SIZE);

		__WpkiPemAfree(symencdek);
		__WpkiPemAfree(symencmic);
	};

	if(status !=WE_SUCCESS)
	{
		WpkiPemKeyInfoDestroy(tmp);
		tmp = WPKI_NULL;
	}

	micalgid->choice   = __KEYINFO;
	micalgid->un.pKeyInfo = tmp;

	return ( status );
}

WpkiStatus
__WpkiPemParserCaseProc19(
					 YYSTYPE ikalgid,
					 YYSTYPE keyinfo
					 )
{
	WpkiStatus status = WE_SUCCESS;
	WpkiUInt32 len = 0;
	WpkiUInt32 realLen = 0;

#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc19()\n");
	/* error */
	if ( (keyinfo == WPKI_NULL)  || (ikalgid == WPKI_NULL)  || (keyinfo->choice != __KEYINFO))
	{
		yyerror("\n error: __WpkiPemParserCaseProc19 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* asymmetric key */
	if(keyinfo->un.pKeyInfo->isKeyAsymmetric)
	{
		keyinfo->un.pKeyInfo->un.asymInfo.ikAlgId = __WpkiPemParserGetIkAlgId(ikalgid);
	}
	/* symmetric case */
	else
	{
		keyinfo->un.pKeyInfo->isKeyAsymmetric   = WPKI_FALSE;
		keyinfo->un.pKeyInfo->un.symInfo.ikAlgId = __WpkiPemParserGetIkAlgId(ikalgid);
	}

	return ( status );
}

WpkiStatus
__WpkiPemParserCaseProc20(
					 YYSTYPE encbin
					 )
{
	WpkiX509CertificateList* tmp;

	WpkiStatus status = WE_SUCCESS;
	WpkiUInt32 len = 0;
	WpkiUInt32 realLen = 0;

	WpkiAsn1Octet *buffer;
    WpkiAsn1Length bufferLen;
    WpkiAsn1Status asnStatus;
	
#ifdef YYDEBUG
	yyerror("Start __WpkiPemParserCaseProc20()\n");
	/* error */
	if (encbin == WPKI_NULL)
	{
		yyerror("\n error: __WpkiPemParserCaseProc20 \n");
		return ( WE_PEM_PARSER_ERROR );
	}
#endif

	/* make WpkiX509SeqOfCertificate object from encbin */
	WPKI_PEM_ALLOC(&tmp, sizeof(WpkiX509CertificateList));

	len = __WpkiPemParserSeqLen(encbin, &realLen, WPKI_TRUE);
	/* Decode from BASE 64 (alloc memory) */
	if((status = _Base64Decode(encbin->value, realLen, &buffer, &bufferLen ))!=WE_SUCCESS)
		return ( WE_PEM_BASE64DECODE_ERR );
	/* Decode from DER to WpkiX509CertificateList */
	if((asnStatus = WpkiAsn1BerDecode(tmp, &TYPE(WpkiX509CertificateList), buffer, bufferLen)) != WPKI_ASN1_SUCCESS)
    {
        /* NOTE: it is currently decided who must free the memory if the decoding has failed */
		WPKI_PEM_FREE(tmp);
		tmp = WPKI_NULL;
		status = WE_PEM_ASN1DECODE_ERR;
    }

	encbin->un.crl    = tmp;
	encbin->choice = __CRL;

	PEM_CLEANUP(buffer);

	return ( status );
}

WpkiPUChar
__FindForward(
			WPKI_CONST WpkiPUChar Text, 
			WPKI_CONST WpkiPUChar  SearchStr
			)
{
#define __MAX_BYTE 256

	WpkiInt32 vfTable[__MAX_BYTE];
	WpkiPUChar result=WPKI_NULL;
	WpkiPUChar tmpText=Text;

	WpkiInt32 iLength = strlen(SearchStr);
	WpkiInt32 iFinish = strlen(Text);
	WpkiInt32 i=iLength-1;

	if (!*Text || !*SearchStr || iLength>iFinish)
		return WPKI_NULL;

	for(i=0; i<__MAX_BYTE; i++) vfTable[i]=iLength;

	for(i=iLength; i>0; i--) vfTable[SearchStr[i]]=i;

	do{
		i = iLength-1;
		// идем сравнивая с конца строки 
		while( (tmpText[i] == SearchStr[i]) && i-->0 ); 

		// если совпадает, то возвратить надо начало совпадения
		if (i==-1)
			result = (char *)tmpText;
		else{
		// если не совпадает, то надо прибавить до возможного совпадения
		// или если вышли за границы проверяемого массива то закончить просмотр
			tmpText = tmpText+vfTable[ SearchStr[i] ];
			iFinish -=vfTable[ SearchStr[i] ];
		};

	}while(result != tmpText && iFinish>0);
	
	return result;
};
		
WpkiStatus
__GetCertHndlByIssuerAndSerial(
    CkSessionHandle     hSession,
    WpkiX509CertSerialNumber  *pSerial,
    WpkiX509Name        *pIssuer, 
    CkObjectHandlePtr   phCertObject
)
{
    WpkiStatus          status = WE_SUCCESS;
    WpkiAsn1Length      len = 0;
    WpkiAsn1Octet       *pOutput = WPKI_NULL;

    WpkiULong           handlesFindCount;
    CkULong             ulCount;
	
	CkCertificateType    certificateType = CKC_X_509;
	CkObjectClass        certificateClass = CKO_CERTIFICATE;

enum
{
	__COUNTER = 4,
    SERIAL_ATTR = 2,
    ISSUER_ATTR = 3
};

    CkAttribute         certSearchTemplate[__COUNTER] = 
    {
        {CKA_CLASS, WPKI_NULL, 0},
        {CKA_CERTIFICATE_TYPE, WPKI_NULL, 0},
        {CKA_SERIAL_NUMBER, WPKI_NULL, 0},
        {CKA_ISSUER, WPKI_NULL, 0}
    };

	SET_TEMPLATE_RECORD(certSearchTemplate, 0, CKA_CLASS, &certificateClass, sizeof(certificateClass));
	SET_TEMPLATE_RECORD(certSearchTemplate, 1, CKA_CERTIFICATE_TYPE, &certificateType, sizeof(certificateType));

	if((pSerial == WPKI_NULL) || (pIssuer == WPKI_NULL))
        return(WE_PEM_INVALID_PARAMS);

    /* DER encode subject */
    if (WE_SUCCESS != (status = WpkiAsn1DerEncode(pSerial, &TYPE(HugeInt), &pOutput, &len)))
        return(status);
    certSearchTemplate[SERIAL_ATTR].pValue = pOutput;
    certSearchTemplate[SERIAL_ATTR].ulValueLen = len;
	
	pOutput = WPKI_NULL;
	len = 0;

    ulCount = sizeof(certSearchTemplate)/sizeof(certSearchTemplate[0]);
    /* DER encode issuer */
    if (WE_SUCCESS != (status = WpkiAsn1DerEncode(pIssuer, &TYPE(WpkiX509Name), &pOutput, &len)))
    {
        WpkiAsn1Free(certSearchTemplate[SERIAL_ATTR].pValue);
        return(status);
    }
    certSearchTemplate[ISSUER_ATTR].pValue = pOutput;
    certSearchTemplate[ISSUER_ATTR].ulValueLen = len;


    status = CkFindObjectsInit(hSession, certSearchTemplate, ulCount);
    if (CKR_OK == status) 
    {
        status = CkFindObjects(hSession, phCertObject, 1, &handlesFindCount);
        CkFindObjectsFinal(hSession);
        if (CKR_OK == status) 
        {
            if (0 == handlesFindCount)
            {
                status = WE_X509_CERT_NOT_FOUND;
                *phCertObject = CK_INVALID_HANDLE;
            }
        }
    }

    WpkiAsn1Free(certSearchTemplate[SERIAL_ATTR].pValue);
    WpkiAsn1Free(certSearchTemplate[ISSUER_ATTR].pValue);

    return(status);
}
