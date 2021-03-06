interface IfcExternalD;
	method Bit#(68) read0_fromDMem_data0();
	method Bit#(1) vread0_fromDMem_data0();
	method Action sread0_fromDMem_data0();
	method Bit#(68) read1_fromDMem_data0();
	method Bit#(1) vread1_fromDMem_data0();
	method Action sread1_fromDMem_data0();
	 (* always_enabled *) method Action write0_fromDMem_data0(Bit#(68) data);
	method Bit#(1) vwrite0_fromDMem_data0();
	method Action swrite0_fromDMem_data0();
	 (* always_enabled *) method Action write1_fromDMem_data0(Bit#(68) data);
	method Bit#(1) vwrite1_fromDMem_data0();
	method Action swrite1_fromDMem_data0();
	method Bit#(1) read0_fromDMem_valid0();
	method Bit#(1) vread0_fromDMem_valid0();
	method Action sread0_fromDMem_valid0();
	method Bit#(1) read1_fromDMem_valid0();
	method Bit#(1) vread1_fromDMem_valid0();
	method Action sread1_fromDMem_valid0();
	 (* always_enabled *) method Action write0_fromDMem_valid0(Bit#(1) data);
	method Bit#(1) vwrite0_fromDMem_valid0();
	method Action swrite0_fromDMem_valid0();
	 (* always_enabled *) method Action write1_fromDMem_valid0(Bit#(1) data);
	method Bit#(1) vwrite1_fromDMem_valid0();
	method Action swrite1_fromDMem_valid0();
	method Bit#(68) read0_toDMem_data0();
	method Bit#(1) vread0_toDMem_data0();
	method Action sread0_toDMem_data0();
	method Bit#(68) read1_toDMem_data0();
	method Bit#(1) vread1_toDMem_data0();
	method Action sread1_toDMem_data0();
	 (* always_enabled *) method Action write0_toDMem_data0(Bit#(68) data);
	method Bit#(1) vwrite0_toDMem_data0();
	method Action swrite0_toDMem_data0();
	 (* always_enabled *) method Action write1_toDMem_data0(Bit#(68) data);
	method Bit#(1) vwrite1_toDMem_data0();
	method Action swrite1_toDMem_data0();
	method Bit#(1) read0_toDMem_valid0();
	method Bit#(1) vread0_toDMem_valid0();
	method Action sread0_toDMem_valid0();
	method Bit#(1) read1_toDMem_valid0();
	method Bit#(1) vread1_toDMem_valid0();
	method Action sread1_toDMem_valid0();
	 (* always_enabled *) method Action write0_toDMem_valid0(Bit#(1) data);
	method Bit#(1) vwrite0_toDMem_valid0();
	method Action swrite0_toDMem_valid0();
	 (* always_enabled *) method Action write1_toDMem_valid0(Bit#(1) data);
	method Bit#(1) vwrite1_toDMem_valid0();
	method Action swrite1_toDMem_valid0();
endinterface
interface IfcExternalI;
	method Bit#(68) read0_fromIMem_data0();
	method Bit#(1) vread0_fromIMem_data0();
	method Action sread0_fromIMem_data0();
	method Bit#(68) read1_fromIMem_data0();
	method Bit#(1) vread1_fromIMem_data0();
	method Action sread1_fromIMem_data0();
	 (* always_enabled *) method Action write0_fromIMem_data0(Bit#(68) data);
	method Bit#(1) vwrite0_fromIMem_data0();
	method Action swrite0_fromIMem_data0();
	 (* always_enabled *) method Action write1_fromIMem_data0(Bit#(68) data);
	method Bit#(1) vwrite1_fromIMem_data0();
	method Action swrite1_fromIMem_data0();
	method Bit#(1) read0_fromIMem_valid0();
	method Bit#(1) vread0_fromIMem_valid0();
	method Action sread0_fromIMem_valid0();
	method Bit#(1) read1_fromIMem_valid0();
	method Bit#(1) vread1_fromIMem_valid0();
	method Action sread1_fromIMem_valid0();
	 (* always_enabled *) method Action write0_fromIMem_valid0(Bit#(1) data);
	method Bit#(1) vwrite0_fromIMem_valid0();
	method Action swrite0_fromIMem_valid0();
	 (* always_enabled *) method Action write1_fromIMem_valid0(Bit#(1) data);
	method Bit#(1) vwrite1_fromIMem_valid0();
	method Action swrite1_fromIMem_valid0();
	method Bit#(68) read0_toIMem_data0();
	method Bit#(1) vread0_toIMem_data0();
	method Action sread0_toIMem_data0();
	method Bit#(68) read1_toIMem_data0();
	method Bit#(1) vread1_toIMem_data0();
	method Action sread1_toIMem_data0();
	 (* always_enabled *) method Action write0_toIMem_data0(Bit#(68) data);
	method Bit#(1) vwrite0_toIMem_data0();
	method Action swrite0_toIMem_data0();
	 (* always_enabled *) method Action write1_toIMem_data0(Bit#(68) data);
	method Bit#(1) vwrite1_toIMem_data0();
	method Action swrite1_toIMem_data0();
	method Bit#(1) read0_toIMem_valid0();
	method Bit#(1) vread0_toIMem_valid0();
	method Action sread0_toIMem_valid0();
	method Bit#(1) read1_toIMem_valid0();
	method Bit#(1) vread1_toIMem_valid0();
	method Action sread1_toIMem_valid0();
	 (* always_enabled *) method Action write0_toIMem_valid0(Bit#(1) data);
	method Bit#(1) vwrite0_toIMem_valid0();
	method Action swrite0_toIMem_valid0();
	 (* always_enabled *) method Action write1_toIMem_valid0(Bit#(1) data);
	method Bit#(1) vwrite1_toIMem_valid0();
	method Action swrite1_toIMem_valid0();
endinterface

interface Ifcrv32;
interface IfcExternalD ifc_ExternalD;
interface IfcExternalI ifc_ExternalI;
endinterface
import "BVI" rv32 = 
module mkrv32(Ifcrv32);
 default_clock clk(CLK);
 default_reset rstn(RST_N);
port rule_ExternalI_input__canfire = 1'b1;
port rule_ExternalD_input__canfire = 1'b1;


	interface IfcExternalD ifc_ExternalD;
		method rule_ExternalD_output_fromDMem_data0_data0 read0_fromDMem_data0();
		method rule_ExternalD_output_fromDMem_data0_data1 read1_fromDMem_data0();
		method  write1_fromDMem_data0(rule_ExternalD_input_fromDMem_data0_data1) enable((*inhigh*) ENExternalDfromDMem_data01);
		method  write0_fromDMem_data0(rule_ExternalD_input_fromDMem_data0_data0) enable((*inhigh*) ENExternalDfromDMem_data00);
		method rule_ExternalD_output_fromDMem_data0_read0 vread0_fromDMem_data0();
		method rule_ExternalD_output_fromDMem_data0_read1 vread1_fromDMem_data0();
		method rule_ExternalD_output_fromDMem_data0_write0 vwrite0_fromDMem_data0();
		method rule_ExternalD_output_fromDMem_data0_write1 vwrite1_fromDMem_data0();
		method  sread0_fromDMem_data0() enable(rule_ExternalD_input_fromDMem_data0_read0);
		method  sread1_fromDMem_data0() enable(rule_ExternalD_input_fromDMem_data0_read1);
		method  swrite0_fromDMem_data0() enable(rule_ExternalD_input_fromDMem_data0_write0);
		method  swrite1_fromDMem_data0() enable(rule_ExternalD_input_fromDMem_data0_write1);
		method rule_ExternalD_output_fromDMem_valid0_data0 read0_fromDMem_valid0();
		method rule_ExternalD_output_fromDMem_valid0_data1 read1_fromDMem_valid0();
		method  write1_fromDMem_valid0(rule_ExternalD_input_fromDMem_valid0_data1) enable((*inhigh*) ENExternalDfromDMem_valid01);
		method  write0_fromDMem_valid0(rule_ExternalD_input_fromDMem_valid0_data0) enable((*inhigh*) ENExternalDfromDMem_valid00);
		method rule_ExternalD_output_fromDMem_valid0_read0 vread0_fromDMem_valid0();
		method rule_ExternalD_output_fromDMem_valid0_read1 vread1_fromDMem_valid0();
		method rule_ExternalD_output_fromDMem_valid0_write0 vwrite0_fromDMem_valid0();
		method rule_ExternalD_output_fromDMem_valid0_write1 vwrite1_fromDMem_valid0();
		method  sread0_fromDMem_valid0() enable(rule_ExternalD_input_fromDMem_valid0_read0);
		method  sread1_fromDMem_valid0() enable(rule_ExternalD_input_fromDMem_valid0_read1);
		method  swrite0_fromDMem_valid0() enable(rule_ExternalD_input_fromDMem_valid0_write0);
		method  swrite1_fromDMem_valid0() enable(rule_ExternalD_input_fromDMem_valid0_write1);
		method rule_ExternalD_output_toDMem_data0_data0 read0_toDMem_data0();
		method rule_ExternalD_output_toDMem_data0_data1 read1_toDMem_data0();
		method  write1_toDMem_data0(rule_ExternalD_input_toDMem_data0_data1) enable((*inhigh*) ENExternalDtoDMem_data01);
		method  write0_toDMem_data0(rule_ExternalD_input_toDMem_data0_data0) enable((*inhigh*) ENExternalDtoDMem_data00);
		method rule_ExternalD_output_toDMem_data0_read0 vread0_toDMem_data0();
		method rule_ExternalD_output_toDMem_data0_read1 vread1_toDMem_data0();
		method rule_ExternalD_output_toDMem_data0_write0 vwrite0_toDMem_data0();
		method rule_ExternalD_output_toDMem_data0_write1 vwrite1_toDMem_data0();
		method  sread0_toDMem_data0() enable(rule_ExternalD_input_toDMem_data0_read0);
		method  sread1_toDMem_data0() enable(rule_ExternalD_input_toDMem_data0_read1);
		method  swrite0_toDMem_data0() enable(rule_ExternalD_input_toDMem_data0_write0);
		method  swrite1_toDMem_data0() enable(rule_ExternalD_input_toDMem_data0_write1);
		method rule_ExternalD_output_toDMem_valid0_data0 read0_toDMem_valid0();
		method rule_ExternalD_output_toDMem_valid0_data1 read1_toDMem_valid0();
		method  write1_toDMem_valid0(rule_ExternalD_input_toDMem_valid0_data1) enable((*inhigh*) ENExternalDtoDMem_valid01);
		method  write0_toDMem_valid0(rule_ExternalD_input_toDMem_valid0_data0) enable((*inhigh*) ENExternalDtoDMem_valid00);
		method rule_ExternalD_output_toDMem_valid0_read0 vread0_toDMem_valid0();
		method rule_ExternalD_output_toDMem_valid0_read1 vread1_toDMem_valid0();
		method rule_ExternalD_output_toDMem_valid0_write0 vwrite0_toDMem_valid0();
		method rule_ExternalD_output_toDMem_valid0_write1 vwrite1_toDMem_valid0();
		method  sread0_toDMem_valid0() enable(rule_ExternalD_input_toDMem_valid0_read0);
		method  sread1_toDMem_valid0() enable(rule_ExternalD_input_toDMem_valid0_read1);
		method  swrite0_toDMem_valid0() enable(rule_ExternalD_input_toDMem_valid0_write0);
		method  swrite1_toDMem_valid0() enable(rule_ExternalD_input_toDMem_valid0_write1);
endinterface

	interface IfcExternalI ifc_ExternalI;
		method rule_ExternalI_output_fromIMem_data0_data0 read0_fromIMem_data0();
		method rule_ExternalI_output_fromIMem_data0_data1 read1_fromIMem_data0();
		method  write1_fromIMem_data0(rule_ExternalI_input_fromIMem_data0_data1) enable((*inhigh*) ENExternalIfromIMem_data01);
		method  write0_fromIMem_data0(rule_ExternalI_input_fromIMem_data0_data0) enable((*inhigh*) ENExternalIfromIMem_data00);
		method rule_ExternalI_output_fromIMem_data0_read0 vread0_fromIMem_data0();
		method rule_ExternalI_output_fromIMem_data0_read1 vread1_fromIMem_data0();
		method rule_ExternalI_output_fromIMem_data0_write0 vwrite0_fromIMem_data0();
		method rule_ExternalI_output_fromIMem_data0_write1 vwrite1_fromIMem_data0();
		method  sread0_fromIMem_data0() enable(rule_ExternalI_input_fromIMem_data0_read0);
		method  sread1_fromIMem_data0() enable(rule_ExternalI_input_fromIMem_data0_read1);
		method  swrite0_fromIMem_data0() enable(rule_ExternalI_input_fromIMem_data0_write0);
		method  swrite1_fromIMem_data0() enable(rule_ExternalI_input_fromIMem_data0_write1);
		method rule_ExternalI_output_fromIMem_valid0_data0 read0_fromIMem_valid0();
		method rule_ExternalI_output_fromIMem_valid0_data1 read1_fromIMem_valid0();
		method  write1_fromIMem_valid0(rule_ExternalI_input_fromIMem_valid0_data1) enable((*inhigh*) ENExternalIfromIMem_valid01);
		method  write0_fromIMem_valid0(rule_ExternalI_input_fromIMem_valid0_data0) enable((*inhigh*) ENExternalIfromIMem_valid00);
		method rule_ExternalI_output_fromIMem_valid0_read0 vread0_fromIMem_valid0();
		method rule_ExternalI_output_fromIMem_valid0_read1 vread1_fromIMem_valid0();
		method rule_ExternalI_output_fromIMem_valid0_write0 vwrite0_fromIMem_valid0();
		method rule_ExternalI_output_fromIMem_valid0_write1 vwrite1_fromIMem_valid0();
		method  sread0_fromIMem_valid0() enable(rule_ExternalI_input_fromIMem_valid0_read0);
		method  sread1_fromIMem_valid0() enable(rule_ExternalI_input_fromIMem_valid0_read1);
		method  swrite0_fromIMem_valid0() enable(rule_ExternalI_input_fromIMem_valid0_write0);
		method  swrite1_fromIMem_valid0() enable(rule_ExternalI_input_fromIMem_valid0_write1);
		method rule_ExternalI_output_toIMem_data0_data0 read0_toIMem_data0();
		method rule_ExternalI_output_toIMem_data0_data1 read1_toIMem_data0();
		method  write1_toIMem_data0(rule_ExternalI_input_toIMem_data0_data1) enable((*inhigh*) ENExternalItoIMem_data01);
		method  write0_toIMem_data0(rule_ExternalI_input_toIMem_data0_data0) enable((*inhigh*) ENExternalItoIMem_data00);
		method rule_ExternalI_output_toIMem_data0_read0 vread0_toIMem_data0();
		method rule_ExternalI_output_toIMem_data0_read1 vread1_toIMem_data0();
		method rule_ExternalI_output_toIMem_data0_write0 vwrite0_toIMem_data0();
		method rule_ExternalI_output_toIMem_data0_write1 vwrite1_toIMem_data0();
		method  sread0_toIMem_data0() enable(rule_ExternalI_input_toIMem_data0_read0);
		method  sread1_toIMem_data0() enable(rule_ExternalI_input_toIMem_data0_read1);
		method  swrite0_toIMem_data0() enable(rule_ExternalI_input_toIMem_data0_write0);
		method  swrite1_toIMem_data0() enable(rule_ExternalI_input_toIMem_data0_write1);
		method rule_ExternalI_output_toIMem_valid0_data0 read0_toIMem_valid0();
		method rule_ExternalI_output_toIMem_valid0_data1 read1_toIMem_valid0();
		method  write1_toIMem_valid0(rule_ExternalI_input_toIMem_valid0_data1) enable((*inhigh*) ENExternalItoIMem_valid01);
		method  write0_toIMem_valid0(rule_ExternalI_input_toIMem_valid0_data0) enable((*inhigh*) ENExternalItoIMem_valid00);
		method rule_ExternalI_output_toIMem_valid0_read0 vread0_toIMem_valid0();
		method rule_ExternalI_output_toIMem_valid0_read1 vread1_toIMem_valid0();
		method rule_ExternalI_output_toIMem_valid0_write0 vwrite0_toIMem_valid0();
		method rule_ExternalI_output_toIMem_valid0_write1 vwrite1_toIMem_valid0();
		method  sread0_toIMem_valid0() enable(rule_ExternalI_input_toIMem_valid0_read0);
		method  sread1_toIMem_valid0() enable(rule_ExternalI_input_toIMem_valid0_read1);
		method  swrite0_toIMem_valid0() enable(rule_ExternalI_input_toIMem_valid0_write0);
		method  swrite1_toIMem_valid0() enable(rule_ExternalI_input_toIMem_valid0_write1);
endinterface

schedule (ifc_ExternalI_read0_toIMem_valid0, ifc_ExternalI_read1_toIMem_valid0, ifc_ExternalI_write0_toIMem_valid0, ifc_ExternalI_write1_toIMem_valid0, ifc_ExternalI_sread0_toIMem_valid0, ifc_ExternalI_sread1_toIMem_valid0, ifc_ExternalI_swrite0_toIMem_valid0, ifc_ExternalI_swrite1_toIMem_valid0, ifc_ExternalI_vread0_toIMem_valid0, ifc_ExternalI_vread1_toIMem_valid0, ifc_ExternalI_vwrite0_toIMem_valid0, ifc_ExternalI_vwrite1_toIMem_valid0, ifc_ExternalI_read0_toIMem_data0, ifc_ExternalI_read1_toIMem_data0, ifc_ExternalI_write0_toIMem_data0, ifc_ExternalI_write1_toIMem_data0, ifc_ExternalI_sread0_toIMem_data0, ifc_ExternalI_sread1_toIMem_data0, ifc_ExternalI_swrite0_toIMem_data0, ifc_ExternalI_swrite1_toIMem_data0, ifc_ExternalI_vread0_toIMem_data0, ifc_ExternalI_vread1_toIMem_data0, ifc_ExternalI_vwrite0_toIMem_data0, ifc_ExternalI_vwrite1_toIMem_data0, ifc_ExternalI_read0_fromIMem_valid0, ifc_ExternalI_read1_fromIMem_valid0, ifc_ExternalI_write0_fromIMem_valid0, ifc_ExternalI_write1_fromIMem_valid0, ifc_ExternalI_sread0_fromIMem_valid0, ifc_ExternalI_sread1_fromIMem_valid0, ifc_ExternalI_swrite0_fromIMem_valid0, ifc_ExternalI_swrite1_fromIMem_valid0, ifc_ExternalI_vread0_fromIMem_valid0, ifc_ExternalI_vread1_fromIMem_valid0, ifc_ExternalI_vwrite0_fromIMem_valid0, ifc_ExternalI_vwrite1_fromIMem_valid0, ifc_ExternalI_read0_fromIMem_data0, ifc_ExternalI_read1_fromIMem_data0, ifc_ExternalI_write0_fromIMem_data0, ifc_ExternalI_write1_fromIMem_data0, ifc_ExternalI_sread0_fromIMem_data0, ifc_ExternalI_sread1_fromIMem_data0, ifc_ExternalI_swrite0_fromIMem_data0, ifc_ExternalI_swrite1_fromIMem_data0, ifc_ExternalI_vread0_fromIMem_data0, ifc_ExternalI_vread1_fromIMem_data0, ifc_ExternalI_vwrite0_fromIMem_data0, ifc_ExternalI_vwrite1_fromIMem_data0, ifc_ExternalD_read0_toDMem_valid0, ifc_ExternalD_read1_toDMem_valid0, ifc_ExternalD_write0_toDMem_valid0, ifc_ExternalD_write1_toDMem_valid0, ifc_ExternalD_sread0_toDMem_valid0, ifc_ExternalD_sread1_toDMem_valid0, ifc_ExternalD_swrite0_toDMem_valid0, ifc_ExternalD_swrite1_toDMem_valid0, ifc_ExternalD_vread0_toDMem_valid0, ifc_ExternalD_vread1_toDMem_valid0, ifc_ExternalD_vwrite0_toDMem_valid0, ifc_ExternalD_vwrite1_toDMem_valid0, ifc_ExternalD_read0_toDMem_data0, ifc_ExternalD_read1_toDMem_data0, ifc_ExternalD_write0_toDMem_data0, ifc_ExternalD_write1_toDMem_data0, ifc_ExternalD_sread0_toDMem_data0, ifc_ExternalD_sread1_toDMem_data0, ifc_ExternalD_swrite0_toDMem_data0, ifc_ExternalD_swrite1_toDMem_data0, ifc_ExternalD_vread0_toDMem_data0, ifc_ExternalD_vread1_toDMem_data0, ifc_ExternalD_vwrite0_toDMem_data0, ifc_ExternalD_vwrite1_toDMem_data0, ifc_ExternalD_read0_fromDMem_valid0, ifc_ExternalD_read1_fromDMem_valid0, ifc_ExternalD_write0_fromDMem_valid0, ifc_ExternalD_write1_fromDMem_valid0, ifc_ExternalD_sread0_fromDMem_valid0, ifc_ExternalD_sread1_fromDMem_valid0, ifc_ExternalD_swrite0_fromDMem_valid0, ifc_ExternalD_swrite1_fromDMem_valid0, ifc_ExternalD_vread0_fromDMem_valid0, ifc_ExternalD_vread1_fromDMem_valid0, ifc_ExternalD_vwrite0_fromDMem_valid0, ifc_ExternalD_vwrite1_fromDMem_valid0, ifc_ExternalD_read0_fromDMem_data0, ifc_ExternalD_read1_fromDMem_data0, ifc_ExternalD_write0_fromDMem_data0, ifc_ExternalD_write1_fromDMem_data0, ifc_ExternalD_sread0_fromDMem_data0, ifc_ExternalD_sread1_fromDMem_data0, ifc_ExternalD_swrite0_fromDMem_data0, ifc_ExternalD_swrite1_fromDMem_data0, ifc_ExternalD_vread0_fromDMem_data0, ifc_ExternalD_vread1_fromDMem_data0, ifc_ExternalD_vwrite0_fromDMem_data0, ifc_ExternalD_vwrite1_fromDMem_data0) CF (ifc_ExternalI_read0_toIMem_valid0, ifc_ExternalI_read1_toIMem_valid0, ifc_ExternalI_write0_toIMem_valid0, ifc_ExternalI_write1_toIMem_valid0, ifc_ExternalI_sread0_toIMem_valid0, ifc_ExternalI_sread1_toIMem_valid0, ifc_ExternalI_swrite0_toIMem_valid0, ifc_ExternalI_swrite1_toIMem_valid0, ifc_ExternalI_vread0_toIMem_valid0, ifc_ExternalI_vread1_toIMem_valid0, ifc_ExternalI_vwrite0_toIMem_valid0, ifc_ExternalI_vwrite1_toIMem_valid0, ifc_ExternalI_read0_toIMem_data0, ifc_ExternalI_read1_toIMem_data0, ifc_ExternalI_write0_toIMem_data0, ifc_ExternalI_write1_toIMem_data0, ifc_ExternalI_sread0_toIMem_data0, ifc_ExternalI_sread1_toIMem_data0, ifc_ExternalI_swrite0_toIMem_data0, ifc_ExternalI_swrite1_toIMem_data0, ifc_ExternalI_vread0_toIMem_data0, ifc_ExternalI_vread1_toIMem_data0, ifc_ExternalI_vwrite0_toIMem_data0, ifc_ExternalI_vwrite1_toIMem_data0, ifc_ExternalI_read0_fromIMem_valid0, ifc_ExternalI_read1_fromIMem_valid0, ifc_ExternalI_write0_fromIMem_valid0, ifc_ExternalI_write1_fromIMem_valid0, ifc_ExternalI_sread0_fromIMem_valid0, ifc_ExternalI_sread1_fromIMem_valid0, ifc_ExternalI_swrite0_fromIMem_valid0, ifc_ExternalI_swrite1_fromIMem_valid0, ifc_ExternalI_vread0_fromIMem_valid0, ifc_ExternalI_vread1_fromIMem_valid0, ifc_ExternalI_vwrite0_fromIMem_valid0, ifc_ExternalI_vwrite1_fromIMem_valid0, ifc_ExternalI_read0_fromIMem_data0, ifc_ExternalI_read1_fromIMem_data0, ifc_ExternalI_write0_fromIMem_data0, ifc_ExternalI_write1_fromIMem_data0, ifc_ExternalI_sread0_fromIMem_data0, ifc_ExternalI_sread1_fromIMem_data0, ifc_ExternalI_swrite0_fromIMem_data0, ifc_ExternalI_swrite1_fromIMem_data0, ifc_ExternalI_vread0_fromIMem_data0, ifc_ExternalI_vread1_fromIMem_data0, ifc_ExternalI_vwrite0_fromIMem_data0, ifc_ExternalI_vwrite1_fromIMem_data0, ifc_ExternalD_read0_toDMem_valid0, ifc_ExternalD_read1_toDMem_valid0, ifc_ExternalD_write0_toDMem_valid0, ifc_ExternalD_write1_toDMem_valid0, ifc_ExternalD_sread0_toDMem_valid0, ifc_ExternalD_sread1_toDMem_valid0, ifc_ExternalD_swrite0_toDMem_valid0, ifc_ExternalD_swrite1_toDMem_valid0, ifc_ExternalD_vread0_toDMem_valid0, ifc_ExternalD_vread1_toDMem_valid0, ifc_ExternalD_vwrite0_toDMem_valid0, ifc_ExternalD_vwrite1_toDMem_valid0, ifc_ExternalD_read0_toDMem_data0, ifc_ExternalD_read1_toDMem_data0, ifc_ExternalD_write0_toDMem_data0, ifc_ExternalD_write1_toDMem_data0, ifc_ExternalD_sread0_toDMem_data0, ifc_ExternalD_sread1_toDMem_data0, ifc_ExternalD_swrite0_toDMem_data0, ifc_ExternalD_swrite1_toDMem_data0, ifc_ExternalD_vread0_toDMem_data0, ifc_ExternalD_vread1_toDMem_data0, ifc_ExternalD_vwrite0_toDMem_data0, ifc_ExternalD_vwrite1_toDMem_data0, ifc_ExternalD_read0_fromDMem_valid0, ifc_ExternalD_read1_fromDMem_valid0, ifc_ExternalD_write0_fromDMem_valid0, ifc_ExternalD_write1_fromDMem_valid0, ifc_ExternalD_sread0_fromDMem_valid0, ifc_ExternalD_sread1_fromDMem_valid0, ifc_ExternalD_swrite0_fromDMem_valid0, ifc_ExternalD_swrite1_fromDMem_valid0, ifc_ExternalD_vread0_fromDMem_valid0, ifc_ExternalD_vread1_fromDMem_valid0, ifc_ExternalD_vwrite0_fromDMem_valid0, ifc_ExternalD_vwrite1_fromDMem_valid0, ifc_ExternalD_read0_fromDMem_data0, ifc_ExternalD_read1_fromDMem_data0, ifc_ExternalD_write0_fromDMem_data0, ifc_ExternalD_write1_fromDMem_data0, ifc_ExternalD_sread0_fromDMem_data0, ifc_ExternalD_sread1_fromDMem_data0, ifc_ExternalD_swrite0_fromDMem_data0, ifc_ExternalD_swrite1_fromDMem_data0, ifc_ExternalD_vread0_fromDMem_data0, ifc_ExternalD_vread1_fromDMem_data0, ifc_ExternalD_vwrite0_fromDMem_data0, ifc_ExternalD_vwrite1_fromDMem_data0);

endmodule
