Require Import Koika.Frontend.

Definition opcode_LOAD      := Ob~0~0~0~0~0~1~1.
Definition opcode_LOAD_FP   := Ob~0~0~0~0~1~1~1.
Definition opcode_MISC_MEM  := Ob~0~0~0~1~1~1~1.
Definition opcode_OP_IMM    := Ob~0~0~1~0~0~1~1.
Definition opcode_AUIPC     := Ob~0~0~1~0~1~1~1.
Definition opcode_OP_IMM_32 := Ob~0~0~1~1~0~1~1.

Definition opcode_STORE     := Ob~0~1~0~0~0~1~1.
Definition opcode_STORE_FP  := Ob~0~1~0~0~1~1~1.
Definition opcode_AMO       := Ob~0~1~0~1~1~1~1.
Definition opcode_OP        := Ob~0~1~1~0~0~1~1.
Definition opcode_LUI       := Ob~0~1~1~0~1~1~1.
Definition opcode_OP_32     := Ob~0~1~1~1~0~1~1.

Definition opcode_MADD := Ob~1~0~0~0~0~1~1.
Definition opcode_MSUB := Ob~1~0~0~0~1~1~1.
Definition opcode_NMSUB := Ob~1~0~0~1~0~1~1.
Definition opcode_NMADD := Ob~1~0~0~1~1~1~1.
Definition opcode_OP_FP := Ob~1~0~1~0~0~1~1.

Definition opcode_BRANCH    := Ob~1~1~0~0~0~1~1.
Definition opcode_JALR      := Ob~1~1~0~0~1~1~1.
Definition opcode_JAL       := Ob~1~1~0~1~1~1~1.
Definition opcode_SYSTEM    := Ob~1~1~1~0~0~1~1.

Definition funct3_LB  := Ob~0~0~0.
Definition funct3_LH  := Ob~0~0~1.
Definition funct3_LW  := Ob~0~1~0.
Definition funct3_LD  := Ob~0~1~1.
Definition funct3_LBU := Ob~1~0~0.
Definition funct3_LHU := Ob~1~0~1.
Definition funct3_LWU := Ob~1~1~0.

Definition funct3_FENCE   := Ob~0~0~0.
Definition funct3_FENCE_I := Ob~0~0~1.

Definition funct3_ADDI  := Ob~0~0~0.
Definition funct3_SLLI  := Ob~0~0~1.
Definition funct3_SLTI  := Ob~0~1~0.
Definition funct3_SLTIU := Ob~0~1~1.
Definition funct3_XORI  := Ob~1~0~0.
Definition funct3_SRLI  := Ob~1~0~1.
Definition funct3_SRAI  := Ob~1~0~1.
Definition funct3_ORI   := Ob~1~1~0.
Definition funct3_ANDI  := Ob~1~1~1.


Definition funct6_SLLI  := Ob~0~0~0~0~0~0.
Definition funct6_SRLI  := Ob~0~0~0~0~0~0.
Definition funct6_SRAI  := Ob~0~1~0~0~0~0.


Definition funct3_ADDIW := Ob~0~0~0.

Definition funct3_SLLIW := Ob~0~0~1.
Definition funct7_SLLIW := Ob~0~0~0~0~0~0~0.

Definition funct3_SRLIW := Ob~1~0~1.
Definition funct7_SRLIW := Ob~0~0~0~0~0~0~0.

Definition funct3_SRAIW := Ob~1~0~1.
Definition funct7_SRAIW := Ob~0~1~0~0~0~0~0.


Definition funct3_SB := Ob~0~0~0.
Definition funct3_SH := Ob~0~0~1.
Definition funct3_SW := Ob~0~1~0.
Definition funct3_SD := Ob~0~1~1.

Definition funct3_ADD  := Ob~0~0~0.
Definition funct7_ADD  := Ob~0~0~0~0~0~0~0.

Definition funct3_SUB  := Ob~0~0~0.
Definition funct7_SUB  := Ob~0~1~0~0~0~0~0.

Definition funct3_SLL  := Ob~0~0~1.
Definition funct7_SLL  := Ob~0~0~0~0~0~0~0.

Definition funct3_SLT  := Ob~0~1~0.
Definition funct7_SLT  := Ob~0~0~0~0~0~0~0.

Definition funct3_SLTU := Ob~0~1~1.
Definition funct7_SLTU := Ob~0~0~0~0~0~0~0.

Definition funct3_XOR  := Ob~1~0~0.
Definition funct7_XOR  := Ob~0~0~0~0~0~0~0.

Definition funct3_SRL  := Ob~1~0~1.
Definition funct7_SRL  := Ob~0~0~0~0~0~0~0.

Definition funct3_SRA  := Ob~1~0~1.
Definition funct7_SRA  := Ob~0~1~0~0~0~0~0.

Definition funct3_OR   := Ob~1~1~0.
Definition funct7_OR   := Ob~0~0~0~0~0~0~0.

Definition funct3_AND  := Ob~1~1~1.
Definition funct7_AND  := Ob~0~0~0~0~0~0~0.

Definition funct3_MUL    := Ob~0~0~0.
Definition funct7_MUL    := Ob~0~0~0~0~0~0~1.

Definition funct3_MULH   := Ob~0~0~1.
Definition funct7_MULH   := Ob~0~0~0~0~0~0~1.

Definition funct3_MULHSU := Ob~0~1~0.
Definition funct7_MULHSU := Ob~0~0~0~0~0~0~1.

Definition funct3_MULHU  := Ob~0~1~1.
Definition funct7_MULHU  := Ob~0~0~0~0~0~0~1.

Definition funct3_DIV    := Ob~1~0~0.
Definition funct7_DIV    := Ob~0~0~0~0~0~0~1.

Definition funct3_DIVU   := Ob~1~0~1.
Definition funct7_DIVU   := Ob~0~0~0~0~0~0~1.

Definition funct3_REM    := Ob~1~1~0.
Definition funct7_REM    := Ob~0~0~0~0~0~0~1.

Definition funct3_REMU   := Ob~1~1~1.
Definition funct7_REMU   := Ob~0~0~0~0~0~0~1.

Definition funct3_ADDW  := Ob~0~0~0.
Definition funct7_ADDW  := Ob~0~0~0~0~0~0~0.

Definition funct3_SUBW  := Ob~0~0~0.
Definition funct7_SUBW  := Ob~0~1~0~0~0~0~0.

Definition funct3_SLLW  := Ob~0~0~1.
Definition funct7_SLLW  := Ob~0~0~0~0~0~0~0.

Definition funct3_SRLW  := Ob~1~0~1.
Definition funct7_SRLW  := Ob~0~0~0~0~0~0~0.

Definition funct3_SRAW  := Ob~1~0~1.
Definition funct7_SRAW  := Ob~0~1~0~0~0~0~0.

Definition funct3_MULW  := Ob~0~0~0.
Definition funct7_MULW  := Ob~0~0~0~0~0~0~1.

Definition funct3_DIVW  := Ob~1~0~0.
Definition funct7_DIVW  := Ob~0~0~0~0~0~0~1.

Definition funct3_DIVUW := Ob~1~0~1.
Definition funct7_DIVUW := Ob~0~0~0~0~0~0~1.

Definition funct3_REMW  := Ob~1~1~0.
Definition funct7_REMW  := Ob~0~0~0~0~0~0~1.

Definition funct3_REMUW := Ob~1~1~1.
Definition funct7_REMUW := Ob~0~0~0~0~0~0~1.

Definition funct3_BEQ  := Ob~0~0~0.
Definition funct3_BNE  := Ob~0~0~1.
Definition funct3_BLT  := Ob~1~0~0.
Definition funct3_BGE  := Ob~1~0~1.
Definition funct3_BLTU := Ob~1~1~0.
Definition funct3_BGEU := Ob~1~1~1.


Definition funct3_PRIV  := Ob~0~0~0.

Definition funct12_ECALL  := Ob~0~0~0~0~0~0~0~0~0~0~0~0.
Definition funct12_EBREAK := Ob~0~0~0~0~0~0~0~0~0~0~0~1.
Definition funct12_URET   := Ob~0~0~0~0~0~0~0~0~0~0~1~0.
Definition funct12_SRET   := Ob~0~0~0~1~0~0~0~0~0~0~1~0.
Definition funct12_MRET   := Ob~0~0~1~1~0~0~0~0~0~0~1~0.
Definition funct12_WFI    := Ob~0~0~0~1~0~0~0~0~0~1~0~1.

Definition funct7_SFENCE_VMA := Ob~0~0~0~1~0~0~1.

Definition funct3_CSRRW  := Ob~0~0~1.
Definition funct3_CSRRS  := Ob~0~1~0.
Definition funct3_CSRRC  := Ob~0~1~1.
Definition funct3_CSRRWI := Ob~1~0~1.
Definition funct3_CSRRSI := Ob~1~1~0.
Definition funct3_CSRRCI := Ob~1~1~1.

Definition funct3_AMOW := Ob~0~1~0.
Definition funct3_AMOD := Ob~0~1~1.

Definition funct5_LR      := Ob~0~0~0~1~0.
Definition funct5_SC      := Ob~0~0~0~1~1.
Definition funct5_AMOSWAP := Ob~0~0~0~0~1.
Definition funct5_AMOADD  := Ob~0~0~0~0~0.
Definition funct5_AMOXOR  := Ob~0~0~1~0~0.
Definition funct5_AMOAND  := Ob~0~1~1~0~0.
Definition funct5_AMOOR   := Ob~0~1~0~0~0.
Definition funct5_AMOMIN  := Ob~1~0~0~0~0.
Definition funct5_AMOMAX  := Ob~1~0~1~0~0.
Definition funct5_AMOMINU := Ob~1~1~0~0~0.
Definition funct5_AMOMAXU := Ob~1~1~1~0~0.

Definition funct3_FLW := Ob~0~1~0.
Definition funct3_FSW := Ob~0~1~0.


Definition funct7_FADD_S := Ob~0~0~0~0~0~0~0.
Definition funct7_FSUB_S := Ob~0~0~0~0~1~0~0.
Definition funct7_FMUL_S := Ob~0~0~0~1~0~0~0.
Definition funct7_FDIV_S := Ob~0~0~0~1~1~0~0.
Definition funct7_FSQRT_S := Ob~0~1~0~1~1~0~0.
Definition funct7_FSGNJ_S := Ob~0~0~1~0~0~0~0.
Definition funct7_FMIN_S := Ob~0~0~1~0~1~0~0.
Definition funct7_FCVT_W_S := Ob~1~1~0~0~0~0~0.
Definition funct7_FMV_X_W := Ob~1~1~1~0~0~0~0.
Definition funct7_FEQ_S := Ob~1~0~1~0~0~0~0.
Definition funct7_FCLASS_S := Ob~1~1~1~0~0~0~0.
Definition funct7_FCVT_S_W := Ob~1~1~0~1~0~0~0.
Definition funct7_FMV_W_X := Ob~1~1~1~1~0~0~0.

Definition funct3_FSGNJ_S := Ob~0~0~0.
Definition funct3_FSGNJN_S := Ob~0~0~1.
Definition funct3_FSGNJX_S := Ob~0~1~0.
Definition funct3_FMIN_S := Ob~0~0~0.
Definition funct3_FMAX_S := Ob~0~0~1.
Definition funct3_FMV_X_W := Ob~0~0~0.
Definition funct3_FEQ_S := Ob~0~1~0.
Definition funct3_FLT_S := Ob~0~0~1.
Definition funct3_FLE_S := Ob~0~0~0.
Definition funct3_FCLASS_S := Ob~0~0~1.

Definition rs2_FCVT_W_S := Ob~0~0~0~0~0.
Definition rs2_FCVT_WU_S := Ob~0~0~0~0~1.
Definition rs2_FCVT_L_S := Ob~0~0~0~1~0.
Definition rs2_FCVT_LU_S := Ob~0~0~0~1~1.
