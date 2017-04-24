
/*---------------------------------------------------------------------------*/
/*--- Provenance Tracking Tool : Dynamic Information Flow System in Valgrind-*/
/*--- Developed by Priyam Biswas --------------------------------------------*/
/*--- Term Project : CS 580 -------------------------------------------------*/
/*---------------------------------------------------------------------------*/



#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"  
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_stacktrace.h"    
#include "pub_tool_libcfile.h"   
#include "pub_tool_addrinfo.h"  

#define __NR_read	3
#define N_EVENTS 4

typedef
   IRExpr 
   IRAtom;

typedef 
   enum { Event_Ir, Event_Dr, Event_Dw, Event_Dm }
   EventKind;

typedef
   struct {
      EventKind  ekind;
      IRAtom*    addr;
      Int        size;
      IRAtom*    guard; 
   }
   Event;

typedef struct taint_source_ty {
	Char	source_val;	
	Addr source_address;

} taint_source;

typedef struct shadow_mem_ty {
	taint_source source_t[50];
	Bool bit_taint;
    Int source_num;

} shadow_mem;

static const HChar* clo_target_path;
static const HChar* clo_trace_path;
static Bool	trace	= False;

static Bool** table = NULL;
static Bool* tempshadow = NULL;
static Bool* reg_shadow = NULL;
static shadow_mem*** table2 = NULL;
static shadow_mem** tempshadow2 = NULL;
static shadow_mem** reg_shadow2 = NULL;

// =====================
static Bool get_shadow_mem(Addr addr) {

	//VG_(printf)("DEBUG: In get Shadow Memory\n");
	Int up = (((addr)&(0xFFFF0000)) >> 16);
	Bool* lookup = table[up];
	if(lookup == NULL)
		return False;
	else {
		Int low = (addr)&(0x0000FFFF);
		return lookup[low];
	}

}
static shadow_mem* get_shadow_mem2(Addr addr) {

	//VG_(printf)("DEBUG: In get SHadow Memory\n");
  Int up = (((addr)&(0xFFFF0000)) >> 16);
	shadow_mem** lookup = table2[up];
	if(lookup == NULL)
		return NULL;
	else {
		Int low = (addr)&(0x0000FFFF);
		return lookup[low];
	}
	 
}

static void set_shadow_mem(Addr addr, Bool value) {

	//VG_(printf)("DEBUG: In set Shadow Memory\n");
	Int up = (((addr)&(0xFFFF0000)) >> 16); 
	Bool* lookup = table[up];
	if(lookup == NULL) { 
		table[up] = (Bool*)VG_(malloc)("Memory shadow", 0xFFFF *sizeof(Bool));
	}
	else {
		Int low = (addr)&(0x0000FFFF);
		lookup[low] = value;
	}

}

static Bool check_taint(shadow_mem* value) {
	if (value == NULL)
		return False;
	else 
		return value->bit_taint;

}

static Int get_source_num(shadow_mem* value) {
	if(value == NULL)
		return 0;
	else
		return value->source_num;
}

static void set_shadow_mem2(Addr addr, shadow_mem* value) {

	//VG_(printf)("DEBUG: In set Shadow Memory\n");
	Int loop_c, i;
	Int up = (((addr)&(0xFFFF0000)) >> 16); 
	shadow_mem** lookup = table2[up];
	if(lookup == NULL) { 
		lookup = table2[up] = (shadow_mem**)VG_(malloc)("Shadow_memory", 0xFFFF *sizeof(shadow_mem*));
		VG_(memset)(lookup, 0, 0xFFFF * sizeof(shadow_mem*));
	}

	Int low = (addr)&(0x0000FFFF);
	shadow_mem* record = lookup[low];
	if(record == NULL) {		
		record = lookup[low] = (shadow_mem*)VG_(malloc)("Shadow_memory", sizeof(shadow_mem));
		VG_(memset)(record, 0, sizeof(shadow_mem));
	}
	
	record->source_num = get_source_num(value);
	//if(check_taint(value)) VG_(printf)("Got true\n");
	//else VG_(printf)("Got False\n");

	record->bit_taint = check_taint(value);
	loop_c = record->source_num;
	i = 0;
	while( i < loop_c) {
		record->source_t[i] = value->source_t[i];
		i = i+ 1;
	}
}

static Bool get_shadow_temp(IRTemp temp){
	return (temp==-1)?False:tempshadow[temp];
}

static  shadow_mem* get_shadow_temp2(IRTemp temp)
{
	//VG_(printf)("DEBUG: In get SHadow temp Memory\n");
	return (temp==-1)?NULL:tempshadow2[temp];

}

static void set_shadow_temp(IRTemp temp, Bool value) {
	tempshadow[temp] = value;
}

static void set_shadow_temp2(IRTemp temp, shadow_mem* value) {

	//VG_(printf)("DEBUG: In set SHadow temp Memory\n");
	Int loop_c, i;
	shadow_mem* record = tempshadow2[temp];
	if(record == NULL) {		
		record = tempshadow2[temp] = (shadow_mem*)VG_(malloc)("Shadow_memory temp", sizeof(shadow_mem));
		VG_(memset)(record, 0, sizeof(shadow_mem));
	}
	
	record->source_num = get_source_num(value);
	record->bit_taint = check_taint(value);

	loop_c = record->source_num;

	i = 0;
	while( i < loop_c) {
		record->source_t[i] = value->source_t[i];
		i = i+ 1;
	}

}

static Bool get_shadow_reg(Int reg_temp){

	//VG_(printf)("DEBUG: In get reg Memory\n");
	return reg_shadow[reg_temp];

}

static shadow_mem* get_shadow_reg2(Int reg_temp)
{
	//VG_(printf)("DEBUG: In get Shadow reg Memory\n");
	return reg_shadow2[reg_temp];

}

static void set_shadow_reg(Int reg_temp, Bool value) {
	reg_shadow[reg_temp] = value;
}

static void set_shadow_reg2(Int reg_temp, shadow_mem* value) {

	//VG_(printf)("DEBUG: In set Shadow reg Memory\n");
	Int loop_c, i;
	shadow_mem* record = reg_shadow2[reg_temp];
	if(record == NULL) {		
		record = reg_shadow2[reg_temp] = (shadow_mem*)VG_(malloc)("Register shadow", sizeof(shadow_mem));
		VG_(memset)(record, 0, sizeof(shadow_mem));
	}
	
	record->source_num = get_source_num(value);
	record->bit_taint = check_taint(value);
	loop_c = record->source_num;
	i = 0;
	while( i < loop_c) {
		record->source_t[i] = value->source_t[i];
		i = i+ 1;
	}

}


/* -------- Shadow Memory end ---------------------------------------------------*/

static void pt_post_clo_init(void) {       //intializing shadow mem

 Int i;
 table = (Bool **)VG_(malloc)("Memory shadow", (0xFFFF) * sizeof(Bool*));
 tempshadow = (Bool *)VG_(malloc)("Temporary shadow", (0xFFFF) * sizeof(Bool));
 reg_shadow = (Bool *)VG_(malloc)("Register shadow", (0xFFFF) * sizeof(Bool));

 table2 = (shadow_mem***)VG_(malloc)("Memory shadow", (0xFFFF) * sizeof(shadow_mem**));
 tempshadow2 = (shadow_mem **)VG_(malloc)("Temporary shadow", (0xFFFF) * sizeof(shadow_mem*));
 reg_shadow2 = (shadow_mem **)VG_(malloc)("Register shadow", (0xFFFF) * sizeof(shadow_mem*));

	for (i=0; i < (0xFFFF); i++) {
		table[i] = NULL;
		tempshadow[i] = False;
		reg_shadow[i] = False;
	}

	for (i=0; i < (0xFFFF); i++) {
		table2[i] = NULL;
		tempshadow2[i] = NULL;
		reg_shadow2[i] = NULL;
	}

}
//====================== From Lackey-- cmdline options================================
static Bool pt_process_cmd_line_option(const HChar* arg)
{
   if VG_STR_CLO(arg, "--target-file", clo_target_path) {}
   else if VG_STR_CLO(arg, "--trace-file", clo_trace_path) {}
   else
      return False;
   
   return True;
}

static void pt_pre_call(ThreadId id, UInt syscallno, UWord* args, UInt nargs) {

//nothing to do for pre_call
}

static void pt_post_call(ThreadId id, UInt syscallno, UWord* args, UInt nargs, SysRes res) {

	SizeT size;
  shadow_mem smem;
	Int i;

	if(trace) {
		if (syscallno == __NR_read) { // read system call

		  VG_(printf)( "reading: arg1: %lx, arg2: %d \n", args[1], args[2]);
			//VG_(printf)( "Read: within IF \n");
     
			for (i = 0; i < (sr_Res(res)); i++) {
					VG_(memset)(&smem, 0, sizeof(shadow_mem));
					smem.bit_taint = True; 
					smem.source_t[0].source_address = args[1] + i;
					smem.source_t[0].source_val = ((Char*)args[1])[i];
					smem.source_num = 1;
					set_shadow_mem2(args[1]+i, &smem);
			}
		
		}
	}
}


static void pt_print_usage(void)
{  
   VG_(printf)(
"    --target-file=<path>     The file as input\n"
"    --trace-file=<path>      The file to print all the trace\n"
   );
}

static Event allevent[N_EVENTS];
static Int fevents = 0;

static Bool source_exist(taint_source* a, taint_source* b, Int* source_num)
{
	Int c; 
	c = 0;

	while(c < source_num) {
		if (b[c].source_address == a->source_address) {
			if (b[c].source_val == a->source_val) {
				return True;
			}
		}
		c = c + 1;
	}
	return False;
}

static void read_in(taint_source* a, taint_source* b, Int* source_num)
{
	Int s_num;
	Int i, j;
	Addr addr;

	s_num = *source_num;

	if(!source_exist(a, b, s_num)) {
		addr = a->source_address;

		for (i = 0; i < s_num; i++) {
			if (b[i].source_address > addr) {
				break;
			}
		}

		for (j = s_num; j > i; j--) {
			b[j] = b[j-1];
		}

		b[i].source_address = a->source_address;
		b[i].source_val = a->source_val;

		(*source_num)++;
		//VG_(printf)("Source Number is %d \n", *source_num); 
	}
}

static VG_REGPARM(2) void trace_instr(Addr addr, SizeT size) {
   VG_(printf)("I  %08lx,%lu\n", addr, size);
}

static VG_REGPARM(2) void trace_load(Addr addr, SizeT size) {
   VG_(printf)(" L %08lx,%lu\n", addr, size);
}

static VG_REGPARM(2) void trace_store(Addr addr, SizeT size) {
   VG_(printf)(" S %08lx,%lu\n", addr, size);
}

static VG_REGPARM(2) void trace_modify(Addr addr, SizeT size) {
   VG_(printf)(" M %08lx,%lu\n", addr, size);
}

static VG_REGPARM(1) void pt_abihint(Addr prog_c) {
	if (trace) {
		//VG_(printf)("pt_abihint-- prog_c: %lx\n", prog_c);
	}
	else
		return;

}

static VG_REGPARM(3) void pt_put(Addr prog_c, Int offset, Int tmp) {

	if (trace) {
		//VG_(printf)("pt_put-- prog_c:%lx, offset: %d, tmp: %d\n", prog_c, offset, tmp);	
		shadow_mem* r_sh = get_shadow_temp2(tmp);
		set_shadow_reg2(offset, r_sh);
	}
}

static VG_REGPARM(2) void pt_puti(Addr prog_c, Int tmp) {
	if (trace) {
		//do nothing just print
		//VG_(printf)("pt_puti-- prog_c:%lx, tmp:%d\n", prog_c, tmp);
	}
	else 
		return;

}

static VG_REGPARM(2) void pt_wrtmp_binder(Addr prog_c, IRTemp tmp) {
	if (trace) {
		//VG_(printf)("pt_wrtmp_binder-- prog_c: %lx, tmp:%d\n", prog_c, tmp);
	}
	else
		return;
}

static VG_REGPARM(3) void pt_wrtmp_get(Addr prog_c, IRTemp tmp, Int offset) {
	if (trace) {
		shadow_mem* s_reg = get_shadow_reg2(offset);
		set_shadow_temp2(tmp, s_reg);
		//VG_(printf)("pt_wrtmp_get-- prog_c: %lx, tmp:%d, offset:%d\n", prog_c, tmp, offset);
	}
	else
		return;
}

static VG_REGPARM(2) void pt_wrtmp_geti(Addr prog_c, IRTemp tmp) {
	
	if (trace) {
		//VG_(printf)("pt_wrtmp_geti-- prog_c: %lx, tmp:%d\n", prog_c, tmp);
	}
	else
		return;

}

static VG_REGPARM(3) void pt_wrtmp_rdtmp(Addr prog_c, IRTemp tmp, Int data) {

	if (trace) {
		shadow_mem* s_mem = get_shadow_temp2(data);
		set_shadow_temp2(tmp, s_mem);
		//VG_(printf)("pt_wrtmp_rdtmp-- prog_c: %lx, tmp:%d, data:%d\n", prog_c, tmp, data);
	}
	else
		return;
}

static VG_REGPARM(3) void pt_wrtmp_qop(Addr prog_c, IRTemp tmp, Int arg1, Int arg2, Int arg3, Int arg4) {

	if (trace) {
		Int i;
		Int loop_c;
		Int c;
		shadow_mem* s_tmp1 = get_shadow_temp2(arg1);
		shadow_mem* s_tmp2 = get_shadow_temp2(arg2);
		shadow_mem* s_tmp3 = get_shadow_temp2(arg3);
		shadow_mem* s_tmp4 = get_shadow_temp2(arg4);
		shadow_mem s_res;

		VG_(memset)(&s_res, 0, sizeof(shadow_mem));

		s_res.bit_taint = check_taint(s_tmp1) | check_taint(s_tmp2);
		s_res.bit_taint = s_res.bit_taint | check_taint(s_tmp3);
		s_res.bit_taint = s_res.bit_taint | check_taint(s_tmp4);
    //==== For arg1 ============
		loop_c = get_source_num(s_tmp1);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp1->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}

		//==== For arg2 ============
		loop_c = get_source_num(s_tmp2);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp2->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}

		//==== For arg3 ============
		loop_c = get_source_num(s_tmp3);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp3->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}

		//==== For arg4 ============
		loop_c = get_source_num(s_tmp4);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp4->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}
   
		set_shadow_temp2(tmp, &s_res);
		//VG_(printf)("pt_wrtmp_qop-- prog_c: %lx, tmp:%d, arg1: %d, arg2: %d, arg3: %d, arg4: %d\n", prog_c, tmp, arg1, arg2, arg3, arg4);
	}
	else
		return;

}

static VG_REGPARM(3) void pt_wrtmp_triop(Addr prog_c, IRTemp tmp, Int arg1, Int arg2, Int arg3) {
	
	if (trace) {
		Int i;
		Int loop_c;
		Int c;
		shadow_mem* s_tmp1 = get_shadow_temp2(arg1);
		shadow_mem* s_tmp2 = get_shadow_temp2(arg2);
		shadow_mem* s_tmp3 = get_shadow_temp2(arg3);
		shadow_mem s_res;

		VG_(memset)(&s_res, 0, sizeof(shadow_mem));

		s_res.bit_taint = check_taint(s_tmp1) | check_taint(s_tmp2);
		s_res.bit_taint = s_res.bit_taint | check_taint(s_tmp3);
    //==== For arg1 ============
		loop_c = get_source_num(s_tmp1);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp1->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}

		//==== For arg2 ============
		loop_c = get_source_num(s_tmp2);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp2->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}

		//==== For arg3 ============
		loop_c = get_source_num(s_tmp3);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp3->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}
   
		set_shadow_temp2(tmp, &s_res);
		//VG_(printf)("pt_wrtmp_triop-- prog_c: %lx, tmp:%d, arg1: %d, arg2: %d, arg3: %d\n", prog_c, tmp, arg1, arg2, arg3);
	}
	else
		return;
}

static VG_REGPARM(3) void pt_wrtmp_binop(Addr prog_c, IRTemp tmp, Int arg1, Int arg2) {

	if (trace) {
		Int i;
		Int loop_c;
		Int c;
		shadow_mem* s_tmp1 = get_shadow_temp2(arg1);
		shadow_mem* s_tmp2 = get_shadow_temp2(arg2);
		shadow_mem s_res;

		VG_(memset)(&s_res, 0, sizeof(shadow_mem));

		s_res.bit_taint = check_taint(s_tmp1) | check_taint(s_tmp2);
    //==== For arg1 ============
		loop_c = get_source_num(s_tmp1);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp1->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}

		//==== For arg2 ============
		loop_c = get_source_num(s_tmp2);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp2->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}
   
		set_shadow_temp2(tmp, &s_res);
		//VG_(printf)("pt_wrtmp_binop-- prog_c: %lx, tmp:%d, arg1: %d, arg2:%d\n", prog_c, tmp, arg1, arg2);
	}
	else
		return;
}

static VG_REGPARM(3) void pt_wrtmp_unop(Addr prog_c, IRTemp tmp, Int arg) {
	
	if (trace) {
		shadow_mem* s_tmp = get_shadow_temp2(arg);
		set_shadow_temp2(tmp, s_tmp);
		//VG_(printf)("pt_wrtmp_unop-- prog_c: %lx, tmp:%d, arg: %d\n", prog_c, tmp, arg);
	}
	else
		return;	
	
}

static VG_REGPARM(3) void pt_wrtmp_load(Addr prog_c, IRTemp tmp, IRTemp addrtmp, Int size, Addr addr) {
	
	if (trace) {	
		shadow_mem s_tmp;
		shadow_mem* s_mem;
		Int i;
		Int c;
		Int loop_c;
		//VG_(printf)("pt_wrtmp_load-- prog_c: %lx, tmp:%d, addr: %lx\n", prog_c, tmp, addr);
		VG_(memset)(&s_tmp, 0, sizeof(shadow_mem));
		
		for (i = 0; i < size; i++) {
			s_mem = get_shadow_mem2(addr+i);

			s_tmp.bit_taint = check_taint(s_mem) | 	s_tmp.bit_taint;
      loop_c = get_source_num(s_mem);
			c = 0;
			while(c < loop_c) {
				read_in(&s_mem->source_t[c], s_tmp.source_t, &s_tmp.source_num);
				c++;
			}
		}

		set_shadow_temp2(tmp, &s_tmp);
	}

}

static VG_REGPARM(2) void pt_wrtmp_const(Addr prog_c, IRTemp tmp) {
	if (trace) {
		//VG_(printf)("pt_wrtmp_const-- prog_c: %lx, tmp:%d\n", prog_c, tmp);
	}
	else
		return;
	
}

static VG_REGPARM(3) void pt_wrtmp_ite(Addr prog_c, IRTemp tmp, Int arg1, Int arg2, Int arg3)
{

  Int c, loop_c;
	if (trace) {	
		shadow_mem* s_mem;
		shadow_mem* s_tmp1 = get_shadow_temp2(arg2);
		shadow_mem* s_tmp2 = get_shadow_temp2(arg3);
		shadow_mem s_res;

		VG_(memset)(&s_res, 0, sizeof(shadow_mem));

		s_res.bit_taint = check_taint(s_tmp1) | check_taint(s_tmp2);
    //==== For iftrue ============
		loop_c = get_source_num(s_tmp1);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp1->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}

		//==== For iffalse ============
		loop_c = get_source_num(s_tmp2);
		c = 0;
		while(c < loop_c) {
			read_in(&s_tmp2->source_t[c], s_res.source_t, &s_res.source_num);
			c++;
		}
   
		set_shadow_temp2(tmp, &s_res);
	}

}

static VG_REGPARM(2) void pt_wrtmp_ccall(Addr prog_c, IRTemp tmp) {
	if (trace) {
		//VG_(printf)("pt_wrtmp_ccall-- prog_c: %lx, tmp:%d\n", prog_c, tmp);
	}
	else
		return;
	
}

static VG_REGPARM(3) void pt_store(Addr prog_c, IRTemp addrtmp, Addr addr, Int tmp, Int size) {

	Int i;
  Int c;
  Int loop_c;
	Addr address;
	Char val;
 

	if (trace) {
		shadow_mem* s_mem = get_shadow_temp2(tmp);
		//VG_(printf)("pt_store-- prog_c: %lx, addr: %lx\n", prog_c, addr);

		for (i = 0; i < size; i++) {
			set_shadow_mem2(addr+i, s_mem);

			if (check_taint(s_mem)) {
        //VG_(printf)("tainted got\n");
				VG_(printf)("Trace -- 0x%08lX [DD]:", addr+i);
		    c = 0;
		    loop_c = get_source_num(s_mem);
				while(c < loop_c) {
					val = s_mem->source_t[c].source_val;
					address = s_mem->source_t[c].source_address;

					if( val == '\n') {
						VG_(printf)(" [mem: 0x%08lX: value: \\n] ", address);
					}
					else
						VG_(printf)(" [mem: 0x%08lX: value: %c] ", address, val);
					c = c +1;
				}
				VG_(printf)("\n\n");
			}
			 //VG_(printf)("not tainted :( \n");
		}
	}

}


static VG_REGPARM(1) void pt_loadg(Addr prog_c) {
	if (trace) {
		//VG_(printf)("pt_load-- prog_c: %lx\n", prog_c);
	}
	else
		return;

}

static VG_REGPARM(1) void pt_storeg(Addr prog_c) {
	if (trace) {
		//VG_(printf)("pt_storeg-- prog_c: %lx\n", prog_c);
	}
	else
		return;

}

static VG_REGPARM(3) void pt_cas(Addr prog_c, Addr addr) {
	if (trace) {	
		//VG_(printf)("pt_cas-- prog_c: %lx, addr: %lx\n", prog_c, addr);
	}
	else 
		return;

}

static VG_REGPARM(3) void pt_llsc(Addr prog_c, IRTemp result, Addr addr, Int storedata) {
	if (trace) {
		//VG_(printf)("pt_llsc-- prog_c: %lx, result: %d, addr: %lx, storedata:%d\n", prog_c, result, addr, storedata);
	}
	else
		return;

}

static VG_REGPARM(1) void pt_dirty(Addr prog_c) {
	if (trace) {
		//VG_(printf)("pt_dirty-- prog_c: %lx\n", prog_c);
	}
	else
		return;

}


static VG_REGPARM(1) void pt_mbe(Addr prog_c) {
	if (trace) {
		//VG_(printf)("pt_mbe-- prog_c: %lx\n", prog_c);
	}
	else
		return;

}


static VG_REGPARM(1) void pt_exit(Addr prog_c) {
	if (trace) {
		//VG_(printf)("pt_exit-- prog_c: %lx\n", prog_c);
	}
	else
		return;
	
}

//=================================== END =================================================

// ================================== Instrumentation =====================================
static
IRSB* pt_instrument ( VgCallbackClosure* closure,
                      IRSB* sbIn,
                      const VexGuestLayout* layout, 
                      const VexGuestExtents* vge,
                      const VexArchInfo* archinfo_host,
                      IRType gWordTy, IRType hWordTy ) {
		IRDirty*	dirty;
		const HChar *fnname;
		IRSB*		sbOut;
		Int i, offset, size;
		//Int i;

		IRTemp tmp;
    IRExpr* data;
		IRExpr*	addr;
		IRExpr** argv;
		IRExpr*	arg1;
		IRExpr* arg2;
		IRExpr*	arg3;
		IRExpr* arg4; 
		IRTypeEnv* env_tmp = sbIn->tyenv;
		Addr prog_c = 0ul;
		 /* Lackey: Set up SB */
		sbOut = deepCopyIRSBExceptStmts(sbIn);

		for (i = 0; i < sbIn->stmts_used; i++) {
			IRStmt *st = sbIn->stmts[i];

			if (!st) continue;
			switch (st->tag) {

				case Ist_IMark:
					prog_c = st->Ist.IMark.addr;
					if(VG_(get_fnname_if_entry)(st->Ist.IMark.addr, &fnname)) {
						if(VG_(strcmp)(fnname, "main") == 0) {
							trace = True;
							//VG_(printf)("printf started\n");
						}
						else if(VG_(strcmp)(fnname, "exit") == 0) {
							trace = False;
						}
					}
					break;

				case Ist_AbiHint:
					argv = mkIRExprVec_1(mkIRExpr_HWord((HWord)prog_c));

					dirty = unsafeIRDirty_0_N(1, "pt_abihint", VG_(fnptr_to_fnentry)(pt_abihint),argv);
					addStmtToIRSB( sbOut, IRStmt_Dirty(dirty));	
					break;

				case Ist_Put:
					
          if(trace) {
						offset = st->Ist.Put.offset;
						data = st->Ist.Put.data;
						//VG_(printf)("Ist_Put offset %d data %d\n", offset, data);
						argv = mkIRExprVec_3( mkIRExpr_HWord( (HWord)prog_c ), mkIRExpr_HWord((HWord)offset), mkIRExpr_HWord( (HWord) ((data->tag == Iex_RdTmp)?(data->Iex.RdTmp.tmp):-1)));

						dirty = unsafeIRDirty_0_N( 3, "pt_put", VG_(fnptr_to_fnentry)(pt_put), argv);
						addStmtToIRSB( sbOut, IRStmt_Dirty(dirty));	
					}
					//addStmtToIRSB( sbOut, st); //
					break; 
				
				case Ist_PutI:

					data = st->Ist.PutI.details->data;
					argv = mkIRExprVec_2( mkIRExpr_HWord( (HWord)prog_c ), mkIRExpr_HWord((HWord) ((data->tag == Iex_RdTmp)?(data->Iex.RdTmp.tmp):-1)));

					dirty = unsafeIRDirty_0_N( 2, "pt_puti", VG_(fnptr_to_fnentry) (pt_puti),argv);
					addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));	
					break;

				case Ist_WrTmp:
					tmp = st->Ist.WrTmp.tmp;
					data = st->Ist.WrTmp.data;

					//================= Start IST_WRTMP  =======
						switch (data->tag) {
								case Iex_Binder:
									argv = mkIRExprVec_2(mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)tmp));
									dirty = unsafeIRDirty_0_N(2, "pt_wrtmp_binder", VG_(fnptr_to_fnentry)(pt_wrtmp_binder), argv);
									addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));
									break;

								case Iex_Get:
								argv = mkIRExprVec_3(mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)tmp ), mkIRExpr_HWord((HWord)data->Iex.Get.offset));
								dirty = unsafeIRDirty_0_N(3, "pt_wrtmp_get", VG_(fnptr_to_fnentry)(pt_wrtmp_get),argv);
								addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));
								break;
	
							case Iex_GetI:
								argv = mkIRExprVec_2(mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)tmp));
								dirty = unsafeIRDirty_0_N( 2, "pt_wrtmp_geti", VG_(fnptr_to_fnentry)(pt_wrtmp_geti), argv );
								addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );
								break;

								case Iex_RdTmp:
									argv = mkIRExprVec_3(mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)tmp), mkIRExpr_HWord((HWord)data->Iex.RdTmp.tmp));
									dirty = unsafeIRDirty_0_N(3, "pt_wrtmp_rdtmp", VG_(fnptr_to_fnentry)(pt_wrtmp_rdtmp),argv);
									addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));
									break;
				
							case Iex_Qop:
								arg1 = data->Iex.Qop.details->arg1;
								arg2 = data->Iex.Qop.details->arg2;
								arg3 = data->Iex.Qop.details->arg3;
								arg4 = data->Iex.Qop.details->arg4;
								argv = mkIRExprVec_6(mkIRExpr_HWord((HWord)prog_c),mkIRExpr_HWord((HWord)tmp), mkIRExpr_HWord((HWord)((arg1->tag == Iex_RdTmp)?(arg1->Iex.RdTmp.tmp):-1)), mkIRExpr_HWord((HWord)((arg2->tag == Iex_RdTmp)?(arg2->Iex.RdTmp.tmp):-1)), mkIRExpr_HWord((HWord)((arg3->tag == Iex_RdTmp)?(arg3->Iex.RdTmp.tmp):-1)), mkIRExpr_HWord((HWord)((arg4->tag == Iex_RdTmp)?(arg4->Iex.RdTmp.tmp):-1)));

								dirty = unsafeIRDirty_0_N( 3, "pt_wrtmp_qop", VG_(fnptr_to_fnentry)(pt_wrtmp_qop), argv); 
								addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );
								break;

							case Iex_Triop:
								arg1 = data->Iex.Triop.details->arg1;
								arg2 = data->Iex.Triop.details->arg2;
								arg3 = data->Iex.Triop.details->arg3;
								argv = mkIRExprVec_5( mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)tmp), mkIRExpr_HWord((HWord)((arg1->tag == Iex_RdTmp)?(arg1->Iex.RdTmp.tmp):-1)),  mkIRExpr_HWord((HWord)((arg2->tag == Iex_RdTmp)?(arg2->Iex.RdTmp.tmp):-1)), mkIRExpr_HWord((HWord)((arg3->tag == Iex_RdTmp)?(arg3->Iex.RdTmp.tmp):-1)));
								dirty = unsafeIRDirty_0_N( 3, "pt_wrtmp_triop", VG_(fnptr_to_fnentry)(pt_wrtmp_triop), argv);
								addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );
								break;

						case Iex_Binop:
								arg1 = data->Iex.Binop.arg1;
								arg2 = data->Iex.Binop.arg2;
								argv = mkIRExprVec_4( mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord( (HWord)tmp ), mkIRExpr_HWord( (HWord)((arg1->tag == Iex_RdTmp)?(arg1->Iex.RdTmp.tmp):-1)), mkIRExpr_HWord((HWord)((arg2->tag == Iex_RdTmp)?(arg2->Iex.RdTmp.tmp):-1)));
								dirty = unsafeIRDirty_0_N( 3, "pt_wrtmp_binop", VG_(fnptr_to_fnentry)(pt_wrtmp_binop), argv);
								addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );
								break;

						case Iex_Unop:
								arg1 = data->Iex.Unop.arg;
								argv = mkIRExprVec_3( mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord( (HWord)tmp),mkIRExpr_HWord((HWord)((arg1->tag == Iex_RdTmp)?(arg1->Iex.RdTmp.tmp):-1)));
								dirty = unsafeIRDirty_0_N( 3, "pt_wrtmp_unop", VG_(fnptr_to_fnentry)(pt_wrtmp_unop), argv);
								addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );
								break;

						case Iex_Load:
								addr = data->Iex.Load.addr;
								size = sizeofIRType(data->Iex.Load.ty);
								argv = mkIRExprVec_5( mkIRExpr_HWord((HWord)prog_c),mkIRExpr_HWord((HWord)tmp), mkIRExpr_HWord((HWord)((addr->tag == Iex_RdTmp)?(addr->Iex.RdTmp.tmp):-1)), mkIRExpr_HWord((HWord)size), addr);
								dirty = unsafeIRDirty_0_N( 3, "pt_wrtmp_load", VG_(fnptr_to_fnentry)(pt_wrtmp_load), argv);
								addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );	
								break;
							
							case Iex_Const:
								argv = mkIRExprVec_3( mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)tmp), mkIRExpr_HWord((HWord)-1));
								dirty = unsafeIRDirty_0_N( 3, "pt_wrtmp_const", VG_(fnptr_to_fnentry)(pt_wrtmp_rdtmp), argv);
								addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );
								break;
						
							case Iex_ITE:
								arg1 = data->Iex.ITE.cond;
								arg2 = data->Iex.ITE.iftrue;
								arg3 = data->Iex.ITE.iffalse;
								argv = mkIRExprVec_5( mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)tmp), mkIRExpr_HWord((HWord)((arg1->tag == Iex_RdTmp)?(arg1->Iex.RdTmp.tmp):-1)),  mkIRExpr_HWord((HWord)((arg2->tag == Iex_RdTmp)?(arg2->Iex.RdTmp.tmp):-1)), mkIRExpr_HWord((HWord)((arg3->tag == Iex_RdTmp)?(arg3->Iex.RdTmp.tmp):-1)));
								dirty = unsafeIRDirty_0_N( 3, "pt_wrtmp_ite", VG_(fnptr_to_fnentry)(pt_wrtmp_ite), argv);
								addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );

							case Iex_CCall:
									argv = mkIRExprVec_2( mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)tmp));
									dirty = unsafeIRDirty_0_N(2, "pt_wrtmp_ccall",VG_(fnptr_to_fnentry)(pt_wrtmp_ccall), argv);
									addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));
									break;

							default:
									break;

							}
					// ========== END IST_WRTMP ====================================
					break;

				case Ist_Store:
					data = st->Ist.Store.data;
					size = sizeofIRType( typeOfIRExpr(env_tmp, data) );
					addr = st->Ist.Store.addr;
					argv = mkIRExprVec_5(mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)((addr->tag == Iex_RdTmp)?addr->Iex.RdTmp.tmp:-1)), addr, mkIRExpr_HWord((HWord)((data->tag == Iex_RdTmp)?(data->Iex.RdTmp.tmp):-1)), mkIRExpr_HWord((HWord)size));
					dirty = unsafeIRDirty_0_N( 3, "pt_store", VG_(fnptr_to_fnentry)(pt_store),argv);
					addStmtToIRSB( sbOut, IRStmt_Dirty(dirty));
					//VG_(printf)("instrumenting store\n");	
					break;

				case Ist_LoadG:
					argv = mkIRExprVec_1( mkIRExpr_HWord( (HWord)prog_c));
					dirty = unsafeIRDirty_0_N( 1, "pt_loadg", VG_(fnptr_to_fnentry) (pt_loadg), argv);
					addStmtToIRSB( sbOut, IRStmt_Dirty(dirty));	
					break;

				case Ist_StoreG:
					argv = mkIRExprVec_1( mkIRExpr_HWord( (HWord)prog_c));
					dirty = unsafeIRDirty_0_N( 1, "pt_storeg", VG_(fnptr_to_fnentry) (pt_storeg), argv);
					addStmtToIRSB( sbOut, IRStmt_Dirty(dirty));	
					break;

				case Ist_CAS:
					addr = st->Ist.CAS.details->addr;
					argv = mkIRExprVec_2( mkIRExpr_HWord((HWord)prog_c),addr);
					dirty = unsafeIRDirty_0_N(2, "pt_cas", VG_(fnptr_to_fnentry)(pt_cas), argv);
					addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );	
					break;

				case Ist_LLSC:
					addr = st->Ist.LLSC.addr;
					data = st->Ist.LLSC.storedata;
					argv = mkIRExprVec_4( mkIRExpr_HWord((HWord)prog_c), mkIRExpr_HWord((HWord)st->Ist.LLSC.result), 	addr, mkIRExpr_HWord((HWord)((data->tag == Iex_RdTmp)?(data->Iex.RdTmp.tmp):-1)));
					dirty = unsafeIRDirty_0_N(3, "pt_llsc", VG_(fnptr_to_fnentry)(pt_llsc), argv);
					addStmtToIRSB( sbOut, IRStmt_Dirty(dirty) );	
					break;

				case Ist_Dirty:
					argv = mkIRExprVec_1( mkIRExpr_HWord( (HWord)prog_c));
					dirty = unsafeIRDirty_0_N( 1, "pt_dirty", VG_(fnptr_to_fnentry) (pt_dirty), argv);
					addStmtToIRSB( sbOut, IRStmt_Dirty(dirty));	
					break;
				
				case Ist_MBE:
					argv = mkIRExprVec_1(mkIRExpr_HWord( (HWord)prog_c));
					dirty = unsafeIRDirty_0_N( 1, "pt_mbe", VG_(fnptr_to_fnentry)(pt_mbe), argv);
					addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));	
					break;

				case Ist_Exit:
					argv = mkIRExprVec_1(mkIRExpr_HWord((HWord)prog_c));
					dirty = unsafeIRDirty_0_N(1, "pt_exit", VG_(fnptr_to_fnentry)(pt_exit), argv);
					addStmtToIRSB( sbOut, IRStmt_Dirty(dirty));	
					break;			

				default:
					break;
			}
		
		addStmtToIRSB( sbOut, st);
	}
  return sbOut;
}


static void pt_fini(Int exitcode)
{
	if (table)
		VG_(free)(table);
	if (table2)
		VG_(free)(table2);
	if (tempshadow)
		VG_(free)(tempshadow);
	if (tempshadow2)
		VG_(free)(tempshadow2);
	if (reg_shadow)
		VG_(free)(reg_shadow);
	if (reg_shadow2)
		VG_(free)(reg_shadow2);

}

static void pt_pre_clo_init(void)
{
   VG_(details_name)            ("Provenance_Tracking");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("Dynamic Information Flow System tool in Valgrind");
   VG_(details_copyright_author)(
      "Developed by Priyam Biswas");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(details_avg_translation_sizeB) ( 200 ); // size from lackey

   VG_(basic_tool_funcs)        (pt_post_clo_init,
                                 pt_instrument,
                                 pt_fini);

	VG_(needs_syscall_wrapper)(pt_pre_call, pt_post_call);

}

VG_DETERMINE_INTERFACE_VERSION(pt_pre_clo_init)

/*---------------------------------------------------------------------------*/
/*--- end --- pt_main.c -----------------------------------------------------*/
/*---------------------------------------------------------------------------*/
