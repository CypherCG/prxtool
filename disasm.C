/***************************************************************
 * PRXTool : Utility for PSP executables.
 * (c) TyRaNiD 2k6
 *
 * disasm.C - Implementation of a MIPS disassembler
 ***************************************************************/

#include <stdio.h>
#include <string.h>
#include "disasm.h"

#include <capstone/capstone.h>

#define INSTR_TYPE_B      1
#define INSTR_TYPE_BL     2

static int g_hexints = 0;
static int g_mregs = 0;
static int g_symaddr = 0;
static int g_macroon = 0;
static int g_printreal = 0;
static int g_printregs = 0;
static int g_regmask = 0;
static int g_printswap = 0;
static int g_signedhex = 0;
static int g_xmloutput = 0;
static SymbolMap *g_syms = NULL;

static int g_opened = 0;
static csh g_handle;

struct DisasmOpt
{
	char opt;
	int *value;
	const char *name;
};

struct DisasmOpt g_disopts[DISASM_OPT_MAX] = {
	{ DISASM_OPT_HEXINTS, &g_hexints, "Hex Integers" },
	{ DISASM_OPT_MREGS, &g_mregs, "Mnemonic Registers" },
	{ DISASM_OPT_SYMADDR, &g_symaddr, "Symbol Address" },
	{ DISASM_OPT_MACRO, &g_macroon, "Macros" },
	{ DISASM_OPT_PRINTREAL, &g_printreal, "Print Real Address" },
	{ DISASM_OPT_PRINTREGS, &g_printregs, "Print Regs" },
	{ DISASM_OPT_PRINTSWAP, &g_printswap, "Print Swap" },
	{ DISASM_OPT_SIGNEDHEX, &g_signedhex, "Signed Hex" },
};

static size_t CAPSTONE_API arm_callback(const uint8_t *code, size_t code_size,
										size_t offset, void *user_data)
{
	return 4;
}

static size_t CAPSTONE_API thumb_callback(const uint8_t *code, size_t code_size,
											size_t offset, void *user_data)
{
	return 2;
}

cs_opt_skipdata g_skipdata_arm = {
	.mnemonic = "Unknown",
	.callback = arm_callback,
};

cs_opt_skipdata g_skipdata_thumb = {
	.mnemonic = "Unknown",
	.callback = thumb_callback,
};

void disasmOpen(int isArm)
{
	if(g_opened)
		return;

	// TODO: only thumb mode supported atm
	isArm = 0;
	cs_open(CS_ARCH_ARM, isArm ? CS_MODE_ARM : CS_MODE_THUMB, &g_handle);
	cs_option(g_handle, CS_OPT_DETAIL, CS_OPT_ON);
	cs_option(g_handle, CS_OPT_SKIPDATA, CS_OPT_ON);
	if(isArm)
		cs_option(g_handle, CS_OPT_SKIPDATA_SETUP, (size_t)&g_skipdata_arm);
	else
		cs_option(g_handle, CS_OPT_SKIPDATA_SETUP, (size_t)&g_skipdata_thumb);

	g_opened = 1;
}

void disasmClose()
{
	if(!g_opened)
		return;

	cs_close(&g_handle);
	g_opened = 0;
}

SymbolType disasmResolveSymbol(unsigned int PC, char *name, int namelen)
{
	SymbolEntry *s;
	SymbolType type = SYMBOL_NOSYM;

	if(g_syms)
	{
		s = (*g_syms)[PC];
		if(s)
		{
			type = s->type;
			snprintf(name, namelen, "%s", s->name.c_str());
		}
	}

	return type;
}

SymbolType disasmResolveRef(unsigned int PC, char *name, int namelen)
{
	SymbolEntry *s;
	SymbolType type = SYMBOL_NOSYM;

	if(g_syms)
	{
		s = (*g_syms)[PC];
		if((s) && (s->imported.size() > 0))
		{
			unsigned int nid = 0;
			PspLibImport *pImp = s->imported[0];

			for(int i = 0; i < pImp->f_count; i++)
			{
				if(strcmp(s->name.c_str(), pImp->funcs[i].name) == 0)
				{
					nid = pImp->funcs[i].nid;
					break;
				}
			}
			type = s->type;
			snprintf(name, namelen, "/%s/%s/nid:0x%08X", pImp->file, pImp->name, nid);
		}
	}

	return type;
}

SymbolEntry* disasmFindSymbol(unsigned int PC)
{
	SymbolEntry *s = NULL;

	if(g_syms)
	{
		s = (*g_syms)[PC];
	}

	return s;
}

int disasmIsBranch(unsigned int opcode, unsigned int *PC, unsigned int *dwTarget)
{
	size_t size = 4;
	uint64_t address;
	const uint8_t *pOpcode;
	cs_insn *insn;
	cs_arm *arm;
	cs_arm_op *op;
	int res;
	int type = 0;

	disasmOpen(0);

	insn = cs_malloc(g_handle);

	address = *PC;
	pOpcode = (const uint8_t *)&opcode;
	res = cs_disasm_iter(g_handle, (const uint8_t **)&pOpcode, &size, (uint64_t *)&address, insn);
	*PC = (unsigned int)address;
	if(res)
	{
		arm = &(insn->detail->arm);

		if(insn->id == ARM_INS_BL || insn->id == ARM_INS_BLX)
		{
			op = &(arm->operands[0]);
			if(op->type == ARM_OP_IMM)
			{
				*dwTarget = op->imm;
				type |= INSTR_TYPE_BL;
			}
		}
		else if(insn->id == ARM_INS_CBZ || insn->id == ARM_INS_CBNZ)
		{
			op = &(arm->operands[1]);
			if(op->type == ARM_OP_IMM)
			{
				*dwTarget = op->imm;
				type |= INSTR_TYPE_B;
			}
		}
		else if(insn->id == ARM_INS_B)
		{
			op = &(arm->operands[0]);
			if(op->type == ARM_OP_IMM)
			{
				*dwTarget = op->imm;
				type |= INSTR_TYPE_B;
			}
		}
	}

	cs_free(insn, 1);

	return type;
}

void disasmAddBranchSymbols(unsigned int opcode, unsigned int *PC, SymbolMap &syms)
{
	SymbolType type;
	int insttype;
	unsigned int addr;
	SymbolEntry *s;
	char buf[128];
	unsigned int oldPC;

	oldPC = *PC;
	insttype = disasmIsBranch(opcode, PC, &addr);
	if(insttype != 0)
	{
		if(insttype & INSTR_TYPE_B)
		{
			snprintf(buf, sizeof(buf), "loc_%08X", addr);
			type = SYMBOL_LOCAL;
		}
		else
		{
			snprintf(buf, sizeof(buf), "sub_%08X", addr);
			type = SYMBOL_FUNC;
		}

		s = syms[addr];
		if(s == NULL)
		{
			s = new SymbolEntry;
			s->addr = addr;
			s->type = type;
			s->size = 0;
			s->name = buf;
			s->refs.insert(s->refs.end(), oldPC);
			syms[addr] = s;
		}
		else
		{
			if((s->type != SYMBOL_FUNC) && (type == SYMBOL_FUNC))
			{
				s->type = SYMBOL_FUNC;
			}
			s->refs.insert(s->refs.end(), oldPC);
		}
	}
}

void disasmSetHexInts(int hexints)
{
	g_hexints = hexints;
}

void disasmSetMRegs(int mregs)
{
	g_mregs = mregs;
}

void disasmSetSymAddr(int symaddr)
{
	g_symaddr = symaddr;
}

void disasmSetMacro(int macro)
{
	g_macroon = macro;
}

void disasmSetPrintReal(int printreal)
{
	g_printreal = printreal;
}

void disasmSetSymbols(SymbolMap *syms)
{
	g_syms = syms;
}

void disasmSetOpts(const char *opts, int set)
{
	while(*opts)
	{
		char ch;
		int i;

		ch = *opts++;
		for(i = 0; i < DISASM_OPT_MAX; i++)
		{
			if(ch == g_disopts[i].opt)
			{
				*g_disopts[i].value = set;
				break;
			}
		}
		if(i == DISASM_OPT_MAX)
		{
			printf("Unknown disassembler option '%c'\n", ch);
		}
	}
}

void disasmPrintOpts(void)
{
	int i;

	printf("Disassembler Options:\n");
	for(i = 0; i < DISASM_OPT_MAX; i++)
	{
		printf("%c : %-3s - %s \n", g_disopts[i].opt, *g_disopts[i].value ? "on" : "off", 
				g_disopts[i].name);
	}
}

static void decode_args(unsigned int opcode, unsigned int PC, const char *fmt, char *output, unsigned int *realregs)
{

}

void format_line(char *code, int codelen, const char *addr, unsigned int opcode, const char *name, const char *args, int noaddr)
{
	char ascii[17];
	char *p;
	int i;

	if(name == NULL)
	{
		name = "Unknown";
		args = "";
	}

	p = ascii;
	for(i = 0; i < 4; i++)
	{
		unsigned char ch;

		ch = (unsigned char) ((opcode >> (i*8)) & 0xFF);
		if((ch < 32) || (ch > 126))
		{
			ch = '.';
		}
		if(g_xmloutput && (ch == '<'))
		{
			strcpy(p, "&lt;");
			p += strlen(p);
		}
		else
		{
			*p++ = ch;
		}
	}
	*p = 0;

	if(noaddr)
	{
		snprintf(code, codelen, "%-10s %s", name, args);
	}
	else
	{
		if(g_printswap)
		{
			if(g_xmloutput)
			{
				snprintf(code, codelen, "%-10s %-80s ; %s: 0x%08X '%s'", name, args, addr, opcode, ascii);
			}
			else
			{
				snprintf(code, codelen, "%-10s %-40s ; %s: 0x%08X '%s'", name, args, addr, opcode, ascii);
			}
		}
		else
		{
			snprintf(code, codelen, "%s: 0x%08X '%s' - %-10s %s", addr, opcode, ascii, name, args);
		}
	}
}

static void decode_args_xml(unsigned int opcode, unsigned int PC, const char *fmt, char *output)
{

}

void format_line_xml(char *code, int codelen, const char *addr, unsigned int opcode, const char *name, const char *args)
{
	char ascii[17];
	char *p;
	int i;

	if(name == NULL)
	{
		name = "Unknown";
		args = "";
	}

	p = ascii;
	for(i = 0; i < 4; i++)
	{
		unsigned char ch;

		ch = (unsigned char) ((opcode >> (i*8)) & 0xFF);
		if((ch < 32) || (ch > 126))
		{
			ch = '.';
		}
		if(g_xmloutput && (ch == '<'))
		{
			strcpy(p, "&lt;");
			p += strlen(p);
		}
		else
		{
			*p++ = ch;
		}
	}
	*p = 0;

	snprintf(code, codelen, "<name>%s</name><opcode>0x%08X</opcode>%s", name, opcode, args);
}

const char *disasmInstruction(unsigned int opcode, unsigned int *PC, unsigned int *realregs, unsigned int *regmask, int noaddr)
{
	static char code[1024];
	const char *name = NULL;
	char args[1024];
	char addr[1024];
	unsigned int dwTarget;
	int i;
	unsigned int oldPC;
	size_t size = 4;
	uint64_t address;
	const uint8_t *pOpcode;
	cs_insn *insn;
	cs_arm *arm;
	cs_arm_op *op;
	int res;
	int symfound = 0;

	sprintf(addr, "0x%08X", *PC);
	if((g_syms) && (g_symaddr))
	{
		char addrtemp[128];
		/* Symbol resolver shouldn't touch addr unless it finds symbol */
		if(disasmResolveSymbol(*PC, addrtemp, sizeof(addrtemp)))
		{
			snprintf(addr, sizeof(addr), "%-20s", addrtemp);
		}
	}

	disasmOpen(0);

	insn = cs_malloc(g_handle);

	oldPC = *PC;
	address = *PC;
	pOpcode = (const uint8_t *)&opcode;
	res = cs_disasm_iter(g_handle, (const uint8_t **)&pOpcode, &size, (uint64_t *)&address, insn);
	*PC = (unsigned int)address;
	if(res)
	{
		arm = &(insn->detail->arm);

		if(insn->id == ARM_INS_BL || insn->id == ARM_INS_BLX)
		{
			op = &(arm->operands[0]);
			if(op->type == ARM_OP_IMM)
			{
				dwTarget = op->imm;
				symfound = disasmResolveSymbol(dwTarget, args, sizeof(args));
			}
		}
		else if(insn->id == ARM_INS_CBZ || insn->id == ARM_INS_CBNZ)
		{
			op = &(arm->operands[1]);
			if(op->type == ARM_OP_IMM)
			{
				dwTarget = op->imm;
				symfound = disasmResolveSymbol(dwTarget, args, sizeof(args));
			}
		}
		else if(insn->id == ARM_INS_B)
		{
			op = &(arm->operands[0]);
			if(op->type == ARM_OP_IMM)
			{
				dwTarget = op->imm;
				symfound = disasmResolveSymbol(dwTarget, args, sizeof(args));
			}
		}

		if(!symfound)
			strncpy(args, insn->op_str, sizeof(args) - 1);

		name = insn->mnemonic;
	}

	if((*PC - oldPC) == 2)
		opcode &= 0xFFFF;

	format_line(code, sizeof(code), addr, opcode, name, args, noaddr);

	cs_free(insn, 1);

	return code;
}

const char *disasmInstructionXML(unsigned int opcode, unsigned int *PC)
{
	// XML output not supported
	(*PC) += 4;
	return "";
}

void disasmSetXmlOutput()
{
	g_xmloutput = 1;
}
