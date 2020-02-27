
typedef struct {
    Bit#(7) opcode;
    Bit#(3) funct3;
    Bit#(7) funct7;
    Bit#(5) funct5;
    Bit#(2) funct2;
    Bit#(5) rd;
    Bit#(5) rs1;
    Bit#(5) rs2;
    Bit#(5) rs3;
    Bit#(32) immI;
    Bit#(32) immS;
    Bit#(32) immB;
    Bit#(32) immU;
    Bit#(32) immJ;
    Bit#(12) csr;
} InstFields deriving (FShow);

function InstFields getInstFields(Bit#(32) inst);
    return InstFields {
        opcode: inst[6:0],
        funct3: inst[14:12],
        funct7: inst[31:25],
        funct5: inst[31:27],
        funct2: inst[26:25],
        rd: inst[11:7],
        rs1: inst[19:15],
        rs2: inst[24:20],
        rs3: inst[31:27],
        immI: signExtend(inst[31:20]),
        immS: signExtend({ inst[31:25], inst[11:7] }),
        immB: signExtend({ inst[31], inst[7], inst[30:25], inst[11:8], 1'b0}),
        immU: signExtend({ inst[31:12], 12'b0 }),
        immJ: signExtend({ inst[31], inst[19:12], inst[20], inst[30:21], 1'b0}),
        csr: inst[31:20]
    };
endfunction

// Opcode Fields
Bit#(7) op_LOAD    = 7'b0000011;
Bit#(7) op_LOADFP  = 7'b0000111;
Bit#(7) op_MISCMEM = 7'b0001111;
Bit#(7) op_OPIMM   = 7'b0010011;
Bit#(7) op_AUIPC   = 7'b0010111;
Bit#(7) op_OPIMM32 = 7'b0011011;
Bit#(7) op_STORE   = 7'b0100011;
Bit#(7) op_STOREFP = 7'b0100111;
Bit#(7) op_AMO     = 7'b0101111;
Bit#(7) op_OP      = 7'b0110011;
Bit#(7) op_LUI     = 7'b0110111;
Bit#(7) op_OP32    = 7'b0111011;
Bit#(7) op_MADD    = 7'b1000011;
Bit#(7) op_MSUB    = 7'b1000111;
Bit#(7) op_NMSUB   = 7'b1001011;
Bit#(7) op_NMADD   = 7'b1001111;
Bit#(7) op_OPFP    = 7'b1010011;
Bit#(7) op_BRANCH  = 7'b1100011;
Bit#(7) op_JALR    = 7'b1100111;
Bit#(7) op_JAL     = 7'b1101111;
Bit#(7) op_SYSTEM  = 7'b1110011;
// 5-bit Opcode Fields
Bit#(5) op5_LOAD    = 5'b00000;
Bit#(5) op5_LOADFP  = 5'b00001;
Bit#(5) op5_MISCMEM = 5'b00011;
Bit#(5) op5_OPIMM   = 5'b00100;
Bit#(5) op5_AUIPC   = 5'b00101;
Bit#(5) op5_OPIMM32 = 5'b00110;
Bit#(5) op5_STORE   = 5'b01000;
Bit#(5) op5_STOREFP = 5'b01001;
Bit#(5) op5_AMO     = 5'b01011;
Bit#(5) op5_OP      = 5'b01100;
Bit#(5) op5_LUI     = 5'b01101;
Bit#(5) op5_OP32    = 5'b01110;
Bit#(5) op5_MADD    = 5'b10000;
Bit#(5) op5_MSUB    = 5'b10001;
Bit#(5) op5_NMSUB   = 5'b10010;
Bit#(5) op5_NMADD   = 5'b10011;
Bit#(5) op5_OPFP    = 5'b10100;
Bit#(5) op5_BRANCH  = 5'b11000;
Bit#(5) op5_JALR    = 5'b11001;
Bit#(5) op5_JAL     = 5'b11011;
Bit#(5) op5_SYSTEM  = 5'b11100;

// Func 3 Fields
// For BRANCH opcode
Bit#(3) fn3_BEQ  = 3'b000;
Bit#(3) fn3_BNE  = 3'b001;
Bit#(3) fn3_BLT  = 3'b100;
Bit#(3) fn3_BGE  = 3'b101;
Bit#(3) fn3_BLTU = 3'b110;
Bit#(3) fn3_BGEU = 3'b111;
// For LOAD, STORE, and AMO opcodes
Bit#(3) fn3_B  = 3'b000;
Bit#(3) fn3_H  = 3'b001;
Bit#(3) fn3_W  = 3'b010;
Bit#(3) fn3_D  = 3'b011;
Bit#(3) fn3_BU = 3'b100;
Bit#(3) fn3_HU = 3'b101;
Bit#(3) fn3_WU = 3'b110;
// For OP, OPIMM, OP32, OPIMM32 opcodes
Bit#(3) fn3_ADDSUB = 3'b000;
Bit#(3) fn3_SLL    = 3'b001;
Bit#(3) fn3_SLT    = 3'b010;
Bit#(3) fn3_SLTU   = 3'b011;
Bit#(3) fn3_XOR    = 3'b100;
Bit#(3) fn3_SR     = 3'b101;
Bit#(3) fn3_OR     = 3'b110;
Bit#(3) fn3_AND    = 3'b111;
// For OP, OP32 opcodes (M-extension)
Bit#(3) fn3_MUL    = 3'b000;
Bit#(3) fn3_MULH   = 3'b001;
Bit#(3) fn3_MULHSU = 3'b010;
Bit#(3) fn3_MULHU  = 3'b011;
Bit#(3) fn3_DIV    = 3'b100;
Bit#(3) fn3_DIVU   = 3'b101;
Bit#(3) fn3_REM    = 3'b110;
Bit#(3) fn3_REMU   = 3'b111;
// For MISCMEM opcode
Bit#(3) fn3_FENCE  = 3'b000;
Bit#(3) fn3_FENCEI = 3'b001;
// For SYSTEM opcode
Bit#(3) fn3_PRIV   = 3'b000;
Bit#(3) fn3_CSRRW  = 3'b001;
Bit#(3) fn3_CSRRS  = 3'b010;
Bit#(3) fn3_CSRRC  = 3'b011;
Bit#(3) fn3_CSRRWI = 3'b101;
Bit#(3) fn3_CSRRSI = 3'b110;
Bit#(3) fn3_CSRRCI = 3'b111;
// funct7 field for SYSTEM opcode
Bit#(7) fn7_SFENCE_VMA = 7'b0001001;

// For AMO opcode
Bit#(5) fn5_LR   = 5'b00010;
Bit#(5) fn5_SC   = 5'b00011;
Bit#(5) fn5_SWAP = 5'b00001;
Bit#(5) fn5_ADD  = 5'b00000;
Bit#(5) fn5_XOR  = 5'b00100;
Bit#(5) fn5_AND  = 5'b01100;
Bit#(5) fn5_OR   = 5'b01000;
Bit#(5) fn5_MIN  = 5'b10000;
Bit#(5) fn5_MAX  = 5'b10100;
Bit#(5) fn5_MINU = 5'b11000;
Bit#(5) fn5_MAXU = 5'b11100;

// For OPFP, MADD, MSUB, NMSUB, and NMADD
// fn2 = funct2 (inst[26:25])
Bit#(2) fn2_S = 2'b00; // single-precision (F-extension)
Bit#(2) fn2_D = 2'b01; // double-precision (D-extension)
// fn5 = funct5 (inst[31:27])
Bit#(5) fn5_FADD           = 5'b00000;
Bit#(5) fn5_FSUB           = 5'b00001;
Bit#(5) fn5_FMUL           = 5'b00010;
Bit#(5) fn5_FDIV           = 5'b00011;
Bit#(5) fn5_FSQRT          = 5'b01011;
Bit#(5) fn5_FSGNJ          = 5'b00100;
Bit#(5) fn5_FMINMAX        = 5'b00101;
Bit#(5) fn5_FCVT_F_F       = 5'b01000; // convert float to float
Bit#(5) fn5_FCVT_I_F       = 5'b11000; // convert float to integer
Bit#(5) fn5_FMV_X_I_FCLASS = 5'b11100; // move bits from fpr to gpr, or the FCLASS instruction
Bit#(5) fn5_FCMP           = 5'b10100; // feq, flt, fle
Bit#(5) fn5_FCVT_F_I       = 5'b11010; // convert integer to float
Bit#(5) fn5_FMV_I_X        = 5'b11110; // move bits from gpr to fpr
// funct3 for fn5_FSGNJ
Bit#(3) fn3_FSGNJ  = 3'b000;
Bit#(3) fn3_FSGNJN = 3'b001;
Bit#(3) fn3_FSGNJX = 3'b010;
// funct3 for fn5_FMINMAX
Bit#(3) fn3_FMIN   = 3'b000;
Bit#(3) fn3_FMAX   = 3'b001;
// funct3 for fn5_FMV_X_I_FCLASS
Bit#(3) fn3_FMV    = 3'b000;
Bit#(3) fn3_FCLASS = 3'b001;
// funct3 for fn5_FCMP
Bit#(3) fn3_FEQ = 3'b010;
Bit#(3) fn3_FLT = 3'b001;
Bit#(3) fn3_FLE = 3'b000;
// rs2 fields (inst[24:20])
Bit#(5) rs2_W  = 5'b00000; // signed 32-bit integer
Bit#(5) rs2_WU = 5'b00001; // unsigned 32-bit integer
Bit#(5) rs2_L  = 5'b00010; // signed 64-bit integer
Bit#(5) rs2_LU = 5'b00011; // unsigned 64-bit integer
Bit#(5) rs2_S  = 5'b00000; // single-precision float (for FCVT_D_S)
Bit#(5) rs2_D  = 5'b00001; // double-precision float (for FCVT_S_D)

// Rounding modes for FPU instructions
Bit#(3) rm_RNE = 3'b000;
Bit#(3) rm_RTZ = 3'b001;
Bit#(3) rm_RDN = 3'b010;
Bit#(3) rm_RUP = 3'b011;
Bit#(3) rm_RMM = 3'b100;
Bit#(3) rm_Dynamic = 3'b111;


function Bool isLegalInstruction(Bit#(32) inst );
    let fields = getInstFields(inst);
    return case (fields.opcode)
        op_LOAD: case (fields.funct3)
                    fn3_B, fn3_H, fn3_W, fn3_BU, fn3_HU: True;
                    default:                             False;
                endcase
        op_OPIMM: case (fields.funct3)
                    fn3_ADDSUB, fn3_SLT, fn3_SLTU, fn3_XOR, fn3_OR, fn3_AND: True;
                    fn3_SLL:                                                 ((fields.funct7[6:1] == 6'b000000) && ((fields.funct7[0] == 1'b0)));
                    fn3_SR:                                                  (((fields.funct7[6:1] == 6'b000000) || (fields.funct7[6:1] == 6'b010000)) && ((fields.funct7[0] == 1'b0)));
                    default:                                                 False;
                endcase
        op_AUIPC: True;
        op_STORE: case (fields.funct3)
                    fn3_B, fn3_H, fn3_W: True;
                    default:             False;
                endcase
        op_OP: (case (fields.funct3)
                    fn3_ADDSUB, fn3_SR:                                   ((fields.funct7 == 7'b0000000) || (fields.funct7 == 7'b0100000));
                    fn3_SLL, fn3_SLT, fn3_SLTU, fn3_XOR, fn3_OR, fn3_AND: (fields.funct7 == 7'b0000000);
                    default:                                              False;
                endcase);
        op_LUI: True;
        op_BRANCH: case (fields.funct3)
                        fn3_BEQ, fn3_BNE, fn3_BLT, fn3_BGE, fn3_BLTU, fn3_BGEU: True;
                        default:                                                False;
                    endcase
        op_JALR: (fields.funct3 == 3'b000);
        op_JAL: True;
        op_SYSTEM: case (fields.funct3)
                        fn3_PRIV: ((fields.rd == 5'b00000) && case ({fields.funct7, fields.rs2}) matches
                                                            12'b000000000000: (fields.rs1 == 5'b00000);        // ECALL
                                                            12'b000000000001: (fields.rs1 == 5'b00000);        // EBREAK
                                                            12'b001100000010: (fields.rs1 == 5'b00000);        // MRET
                                                            12'b000100000101: (fields.rs1 == 5'b00000);        // WFI
                                                            default:          False;
                                                        endcase);
                        default:                                                             False;
                    endcase
        default: False;
    endcase;
endfunction


typedef enum {
    ImmI,
    ImmS,
    ImmB,
    ImmU,
    ImmJ
} ImmediateType deriving (Bits, Eq, FShow);

function Maybe#(ImmediateType) getImmediateTypeFrom32BitInst(Bit#(32) inst);
    return (case (inst[6:2])
                op5_LOAD, op5_LOADFP, op5_OPIMM, op5_OPIMM32, op5_JALR: tagged Valid ImmI;
                op5_AUIPC, op5_LUI:                                     tagged Valid ImmU;
                op5_STORE, op5_STOREFP:                                 tagged Valid ImmS;
                op5_BRANCH:                                             tagged Valid ImmB;
                op5_JAL:                                                tagged Valid ImmJ;
                default:                                                tagged Invalid;
            endcase);
endfunction

function Bit#(32) getImmediate(DecodedInst dInst);
    return case (dInst.immediateType)
                tagged Valid ImmI: getImmediateI(dInst.inst);
                tagged Valid ImmS: getImmediateS(dInst.inst);
                tagged Valid ImmB: getImmediateB(dInst.inst);
                tagged Valid ImmU: getImmediateU(dInst.inst);
                tagged Valid ImmJ: getImmediateJ(dInst.inst);
                default: 0;
            endcase;
endfunction


typedef struct {
    Bool                    legal;
    Bool         valid_rs1;
    Bool         valid_rs2;
    Bool         valid_rd;
    Maybe#(ImmediateType)   immediateType;
    Bit#(32)                inst;
} DecodedInst deriving (Bits, Eq, FShow);

function Bit#(xlen) getImmediateI(Bit#(32) inst) provisos (Add#(32, a__, xlen));
    Bit#(32) imm32 = signExtend(inst[31:20]);
    return signExtend(imm32);
endfunction
function Bit#(xlen) getImmediateS(Bit#(32) inst) provisos (Add#(32, a__, xlen));
    Bit#(32) imm32 = signExtend({ inst[31:25], inst[11:7] });
    return signExtend(imm32);
endfunction
function Bit#(xlen) getImmediateB(Bit#(32) inst) provisos (Add#(32, a__, xlen));
    Bit#(32) imm32 = signExtend({ inst[31], inst[7], inst[30:25], inst[11:8], 1'b0});
    return signExtend(imm32);
endfunction
function Bit#(xlen) getImmediateU(Bit#(32) inst) provisos (Add#(32, a__, xlen));
    Bit#(32) imm32 = signExtend({ inst[31:12], 12'b0 });
    return signExtend(imm32);
endfunction
function Bit#(xlen) getImmediateJ(Bit#(32) inst) provisos (Add#(32, a__, xlen));
    Bit#(32) imm32 = signExtend({ inst[31], inst[19:12], inst[20], inst[30:21], 1'b0});
    return signExtend(imm32);
endfunction


function Bool usesRD(Bit#(32) inst);
    return case (inst[6:2])
            5'b01101: True; // lui
            5'b11011: True; // jal
            5'b00000: True; // lh, ld, lw, lwu, lbu, lhu, lb
            5'b01100: True; // sll, mulh, sltu, mulhu, slt, mulhsu, or, rem, xor, div, and, remu, srl, divu, sra, add, mul, sub
            5'b11001: True; // jalr
            5'b00100: True; // srli, srli, srai, srai, slli, slli, ori, sltiu, andi, slti, addi, xori
            5'b00101: True; // auipc
            default: False;
        endcase;
endfunction

function Bool usesRS1(Bit#(32) inst);
    return case (inst[6:2])
               5'b11000: True; // bge, bne, bltu, blt, bgeu, beq
               5'b00000: True; // lh, ld, lw, lwu, lbu, lhu, lb
               5'b01000: True; // sh, sb, sw, sd
               5'b01100: True; // sll, mulh, sltu, mulhu, slt, mulhsu, or, rem, xor, div, and, remu, srl, divu, sra, add, mul, sub
               5'b11001: True; // jalr
               5'b00100: True; // srli, srli, srai, srai, slli, slli, ori, sltiu, andi, slti, addi, xori
               default: False;
           endcase;
endfunction

function Bool usesRS2(Bit#(32) inst);
    return case (inst[6:2])
               5'b11000: True; // bge, bne, bltu, blt, bgeu, beq
               5'b01000: True; // sh, sb, sw, sd
               5'b01100: True; // sll, mulh, sltu, mulhu, slt, mulhsu, or, rem, xor, div, and, remu, srl, divu, sra, add, mul, sub
               default: False;
        endcase;
endfunction

function DecodedInst decodeInst(Bit#(32) input_inst);

    Bool legal_encoding = isLegalInstruction(input_inst);
    Bit#(32) inst =  input_inst;
    Maybe#(ImmediateType) immediate_type = getImmediateTypeFrom32BitInst(inst);

    return DecodedInst {
            legal: legal_encoding,
            valid_rs1: usesRS1(inst),
            valid_rs2: usesRS2(inst),
            valid_rd: usesRD(inst),
            immediateType: immediate_type,
            inst: inst
        };
endfunction

function Bit#(32) execALU32(Bit#(32) inst, Bit#(32) rs1_val, Bit#(32) rs2_val, Bit#(32) imm_val, Bit#(32) pc);
    // isAUIPCorLUI = inst[2]
    // isLUI = inst[5]
    // isNotIMM = inst[5]
    Bool isLUI = (inst[2] == 1'b1) && (inst[5] == 1'b1);
    Bool isAUIPC = (inst[2] == 1'b1) && (inst[5] == 1'b0);
    Bool isIMM = (inst[5] == 1'b0);
    Bit#(32) rd_val = 0;
    if (isLUI) begin
        rd_val = imm_val;
    end else if (isAUIPC) begin
        rd_val = pc + imm_val;
    end else begin
        Bit#(32) alu_src1 = rs1_val;
        Bit#(32) alu_src2 = isIMM ? imm_val : rs2_val;
        Bit#(3) funct3 = inst[14:12];
        Bit#(1) inst_30 = inst[30];
        if ((funct3 == fn3_ADDSUB) && isIMM) begin
            // this is a special caes for addi
            inst_30 = 0;
        end
        rd_val = alu32(funct3, inst_30, alu_src1, alu_src2);
    end

    return rd_val;
endfunction

function Bit#(32) alu32(Bit#(3) funct3, Bit#(1) inst_30, Bit#(32) a, Bit#(32) b);
    // setup inputs
    Bool isSRA = (funct3 == 3'b101) && (inst_30 == 1'b1);
    Bit#(5) shamt = truncate(b);

    Bit#(32) res = (case(funct3)
            fn3_ADDSUB: (inst_30 == 1'b1 ? a - b : a + b);
            fn3_SLL:    (a << shamt);
            fn3_SLT:    zeroExtend(pack(signedLT(a, b)));
            fn3_SLTU:   zeroExtend(pack(a < b));
            fn3_XOR:    (a ^ b);
            fn3_SR:     (inst_30 == 1'b1 ? signedShiftRight(a, shamt) : a >> shamt);
            fn3_OR:     (a | b);
            fn3_AND:    (a & b);
            default:    0;
        endcase);

    return res;
endfunction


typedef struct {
    Bool taken;
    Bit#(32) nextPC;
} ControlResult deriving (Bits, Eq, FShow);


function ControlResult execControl32(Bit#(32) inst, Bit#(32) rs1_val, Bit#(32) rs2_val, Bit#(32) imm_val, Bit#(32) pc);
    Bool isControl = inst[6:4] == 3'b110;
    Bool isJAL = (inst[2] == 1'b1) && (inst[3] == 1'b1);
    Bool isJALR = (inst[2] == 1'b1) && (inst[3] == 1'b0);

    Bit#(32) incPC = pc + 4;
    Bit#(3) funct3 = inst[14:12];

    Bool taken = True; // for JAL and JALR
    Bit#(32) nextPC = incPC;
    Bit#(32) rd_val = pc; // for JAL and JALR

    if (!isControl) begin
        // not a control instruction
        taken = False;
        nextPC = incPC;
    end else if (isJAL) begin
        taken = True;
        nextPC = pc + imm_val;
    end else if (isJALR) begin
        taken = True;
        nextPC = (rs1_val + imm_val) & ~1; // zero out LSB
    end else begin
        // Branch
        taken = case (funct3)
                    fn3_BEQ:    (rs1_val == rs2_val);
                    fn3_BNE:    (rs1_val != rs2_val);
                    fn3_BLT:    signedLT(rs1_val, rs2_val);
                    fn3_BGE:    signedGE(rs1_val, rs2_val);
                    fn3_BLTU:   (rs1_val < rs2_val);
                    fn3_BGEU:   (rs1_val >= rs2_val);
                endcase;
        if (taken) begin
            nextPC = pc + imm_val;
        end else begin
            nextPC = incPC;
        end
    end

    return ControlResult{ taken: taken, nextPC: nextPC };
endfunction

// function Bool isBRANCH(DecodedInst dInst);
//     return isControlInst(dInst) && (dInst.inst[2] == 1'b0);
// endfunction
// function Bool isJALR(DecodedInst dInst);
//     return isControlInst(dInst) && (dInst.inst[3:2] == 2'b01);
// endfunction
// function Bool isJAL(DecodedInst dInst);
//     return isControlInst(dInst) && (dInst.inst[3:2] == 2'b11);
// endfunction

// Instruction Classes
function Bool isMemoryInst(DecodedInst dInst);
    return (dInst.inst[6] == 1'b0) && (dInst.inst[4:3] == 2'b00);
endfunction

function Bool isControlInst(DecodedInst dInst);
    return (dInst.inst[6:4] == 3'b110); // This also covers a reserved opcode
endfunction

