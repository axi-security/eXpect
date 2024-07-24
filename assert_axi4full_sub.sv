module assert_axi4full (
  // Global Clock Signal
  input wire  S_AXI_ACLK,
  // Global Reset Signal. This Signal is Active LOW
  input wire  S_AXI_ARESETN,
  // Write address (issued by master, acceped by Slave)
  input wire [3 : 0] S_AXI_AWADDR,
  // Write channel Protection type. This signal indicates the
  // privilege and security level of the transaction, and whether
  // the transaction is a data access or an instruction access.
  input wire [2 : 0] S_AXI_AWPROT,
  // Write address valid. This signal indicates that the master signaling
  // valid write address and control information.
  input wire  S_AXI_AWVALID,
  // Write data (issued by master, acceped by Slave)
  input wire [31 : 0] S_AXI_WDATA,
  // Write strobes. This signal indicates which byte lanes hold
  // valid data. There is one write strobe bit for each eight
  // bits of the write data bus.
  input wire [3 : 0] S_AXI_WSTRB,
  // Write last. This signal indicates the last transfer
  // in a write burst.
  input wire  S_AXI_WLAST,
  // Write valid. This signal indicates that valid write
  // data and strobes are available.
  input wire  S_AXI_WVALID,
  // Response ready. This signal indicates that the master
  // can accept a write response.
  input wire  S_AXI_BREADY,
// Read address (issued by master, acceped by Slave)
  input wire [3 : 0] S_AXI_ARADDR,
  // Protection type. This signal indicates the privilege
  // and security level of the transaction, and whether the
  // transaction is a data access or an instruction access.
  input wire [2 : 0] S_AXI_ARPROT,
  // Read address valid. This signal indicates that the channel
  // is signaling valid read address and control information.
  input wire  S_AXI_ARVALID,
  // Read ready. This signal indicates that the master can
  // accept the read data and response information.
  input wire  S_AXI_RREADY
 );

// Read Transaction, Channel Ordering
P_1 : assert property (@(posedge S_AXI_ACLK) (S_AXI_ARESETN && S_AXI_ARVALID && my_source.S_AXI_ARREADY) |-> (!(my_source.S_AXI_RVALID)));

// Write Transaction, Channel Ordering
P_2 : assert property (@(posedge S_AXI_ACLK) (S_AXI_ARESETN && S_AXI_WVALID && my_source.S_AXI_WREADY) |-> (!(my_source.S_AXI_BVALID)));

// Read Transaction, Stability, AR Channel
P_3_AR : assert property (@(posedge S_AXI_ACLK) disable iff ((S_AXI_ARVALID == 1) && (my_source.S_AXI_ARREADY == 1)) ((S_AXI_ARESETN == 1) && (S_AXI_ARVALID) && (!my_source.S_AXI_ARREADY)) |=> (S_AXI_ARVALID == 1));

// Read Transaction, Stability, R Channel
P_3_R: assert property (@(posedge S_AXI_ACLK) disable iff ((my_source.S_AXI_RVALID == 1) && (S_AXI_RREADY == 1)) ((S_AXI_ARESETN == 1) && my_source.S_AXI_RVALID && (!S_AXI_RREADY)) |=> (my_source.S_AXI_RVALID == 1));

// Write Transaction, Stability, AW Channel
P_3_AW : assert property (@(posedge S_AXI_ACLK) ((S_AXI_ARESETN == 1) && S_AXI_AWVALID && (!my_source.S_AXI_AWREADY)) |=> (S_AXI_AWVALID == 1));

// Write Transaction, Stability, W Channel
P_3_W: assert property (@(posedge S_AXI_ACLK) disable iff ((S_AXI_WVALID == 1) && (my_source.S_AXI_WREADY == 1)) ((S_AXI_ARESETN == 1) && S_AXI_WVALID && (!my_source.S_AXI_WREADY)) |=> (S_AXI_WVALID == 1));


// Write Transaction, Stability, B Channel
P_3_B: assert property (@(posedge S_AXI_ACLK) disable iff ((my_source.S_AXI_BVALID == 1) && (S_AXI_BREADY == 1)) ((S_AXI_ARESETN == 1) && my_source.S_AXI_BVALID && (!S_AXI_BREADY)) |=> (my_source.S_AXI_BVALID == 1));

// Read Transaction, Stability, ARADDR
P_4_AR: assert property (@(posedge S_AXI_ACLK) disable iff ((S_AXI_ARVALID == 1) && (my_source.S_AXI_ARREADY == 1)) ((S_AXI_ARESETN == 1 ) && (S_AXI_ARVALID) && (!my_source.S_AXI_ARREADY)) |=> ($past(S_AXI_ARADDR) == S_AXI_ARADDR));

// Write Transaction, Stability, AWADDR
P_4_AW : assert property (@(posedge S_AXI_ACLK) disable iff ((S_AXI_AWVALID == 1) && (my_source.S_AXI_AWREADY == 1)) ((S_AXI_ARESETN == 1) && S_AXI_AWVALID && (!my_source.S_AXI_AWREADY)) |=>  $stable(S_AXI_AWADDR));

// Read Transaction, Stability, ARPROT
P_5_AR: assert property (@(posedge S_AXI_ACLK) disable iff ((S_AXI_ARVALID == 1) && (my_source.S_AXI_ARREADY == 1)) ((S_AXI_ARESETN == 1) && $rose(S_AXI_ARVALID) && (!my_source.S_AXI_ARREADY)) |=> ($past(S_AXI_ARPROT) == S_AXI_ARPROT));

// Read Transaction, Stability, ARPROT
P_5_AR: assert property (@(posedge S_AXI_ACLK) disable iff ((S_AXI_ARVALID == 1) && (my_source.S_AXI_ARREADY == 1)) ((S_AXI_ARESETN == 1) && $rose(S_AXI_ARVALID) && (!my_source.S_AXI_ARREADY)) |=> ($past(S_AXI_ARPROT) == S_AXI_ARPROT));

// Read Transaction, Stability, AWPROT
P_5_AW : assert property (@(posedge S_AXI_ACLK) disable iff ((S_AXI_AWVALID == 1) && (my_source.S_AXI_AWREADY == 1)) ((S_AXI_ARESETN == 1) && S_AXI_AWVALID && (!my_source.S_AXI_AWREADY)) |=> $stable(S_AXI_AWPROT));

// Reset Mechanism, Subordinate driven, Handshake signals
P_6_1 : assert property (@(posedge S_AXI_ACLK) ($rose(S_AXI_ARESETN)) |-> (!S_AXI_ARVALID && !S_AXI_AWVALID && !S_AXI_WVALID));

// Reset Mechanism, Subordinate driven, Handshake signals
P_6_2 : assert property (@(posedge S_AXI_ACLK) ($fell(S_AXI_ARESETN)) |-> ##1 (!S_AXI_ARVALID && !S_AXI_AWVALID && !S_AXI_WVALID));

// Reset Mechanism, Subordinate driven, Handshake signals
P_7_1 : assert property (@(posedge S_AXI_ACLK) ($rose(S_AXI_ARESETN)) |-> (!my_source.S_AXI_RVALID && !my_source.S_AXI_BVALID));
// Reset Mechanism, Subordinate driven, Handshake signals
P_7_2 : assert property (@(posedge S_AXI_ACLK) ($fell(S_AXI_ARESETN)) |-> ##1 (!my_source.S_AXI_RVALID && !my_source.S_AXI_BVALID));

// Read Transaction, Sensitive Data Stability, RDATA
P_8_R : assert property (@(posedge S_AXI_ACLK) disable iff ((my_source.S_AXI_RVALID == 1) && (S_AXI_RREADY == 1)) ((S_AXI_ARESETN == 1) && my_source.S_AXI_RVALID && (!S_AXI_RREADY)) |=> ($stable(my_source.S_AXI_RDATA)));

// Write Transaction, Sensitive Data Stability, WDATA
P_8_W : assert property (@(posedge S_AXI_ACLK) disable iff ((S_AXI_WVALID == 1) && (my_source.S_AXI_WREADY == 1)) ((S_AXI_ARESETN == 1) && S_AXI_WVALID && (!my_source.S_AXI_WREADY)) |=> $stable(S_AXI_WDATA));

// Read Transaction, Sensitive Data Stability, RRESP
P_9_R : assert property (@(posedge S_AXI_ACLK) disable iff ((my_source.S_AXI_RVALID == 1) && (S_AXI_RREADY == 1)) ((S_AXI_ARESETN == 1) && my_source.S_AXI_RVALID && (!S_AXI_RREADY)) |=> $stable(my_source.S_AXI_RRESP));

// Write Transaction, Sensitive Data Stability, BRESP
P_9_B: assert property (@(posedge S_AXI_ACLK) disable iff ((my_source.S_AXI_BVALID == 1) && (S_AXI_BREADY == 1)) ((S_AXI_ARESETN == 1) && my_source.S_AXI_BVALID && (!S_AXI_BREADY)) |=> $stable(my_source.S_AXI_BRESP));

// Read Transaction, Strict Ordering
P_11 : assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (S_AXI_ARVALID & my_source.S_AXI_ARREADY) implies (!my_source.S_AXI_RVALID) [*1:$] ##1 (my_source.S_AXI_RVALID && S_AXI_RREADY));

// Write Transaction, Strict Ordering
P_12 : assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (S_AXI_AWVALID & my_source.S_AXI_AWREADY) implies (!my_source.S_AXI_WREADY) [*1:$] ##1 (my_source.S_AXI_WREADY && S_AXI_WVALID));

// Write Transaction, Strict Ordering
P_13 : assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (S_AXI_AWVALID & my_source.S_AXI_AWREADY) ##1 (S_AXI_WVALID & my_source.S_AXI_WREADY) implies (!my_source.S_AXI_BVALID) [*1:$] ##1 (my_source.S_AXI_BVALID && S_AXI_BREADY));

// Reset Mechanism, Subordinate driven, RDATA and RESP
P_14_1 : assert property (@(posedge S_AXI_ACLK) ($rose(S_AXI_ARESETN)) |-> ((my_source.S_AXI_RDATA == 0) && (my_source.S_AXI_RRESP == 2'b00) && (my_source_.S_AXI_BRESP == 2'b00)));
// Reset Mechanism, Subordinate driven, RDATA and RESP
P_14_2 : assert property (@(posedge S_AXI_ACLK) ($fell(S_AXI_ARESETN)) |-> ##1 ((my_source.S_AXI_RDATA == 0) && (my_source.S_AXI_RRESP == 2'b00) && (my_source_.S_AXI_BRESP == 2'b00)));

// Reset Mechanism, Manager drive, ADDR, WDATA, PROT
P_15_1 : assert property (@(posedge S_AXI_ACLK) ($rose(S_AXI_ARESETN)) |-> ((S_AXI_ARADDR == 0) && (S_AXI_AWADDR == 0) && (S_AXI_WDATA == 0) && (S_AXI_ARPROT == 3'b000) && (S_AXI_AWPROT == 3'b000)));

// Reset Mechanism, Manager driven, ADDR, WDATA, PROT
P_15_2 : assert property (@(posedge S_AXI_ACLK) ($fell(S_AXI_ARESETN)) |-> ##1 ((S_AXI_ARADDR == 0) && (S_AXI_AWADDR == 0) && (S_AXI_WDATA == 0) && (S_AXI_ARPROT == 3'b000) && (S_AXI_AWPROT == 3'b000)));

// Read Transaction, Subordinate driven, Data Invalidation
P_16 : assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (!my_source.S_AXI_RVALID) |-> my_source.S_AXI_RDATA == 0);

// Write Transaction, Manager driven, LAST Signal
P_17_W : assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (S_AXI_WLAST) |-> (S_AXI_WVALID));

// Read Transaction, Subordinate driven, LAST Signal
P_17_R : assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (my_source.S_AXI_RLAST) |-> (my_source.S_AXI_RVALID));

// Read Transaction, Strict Ordering AXI4 
P_18: assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (S_AXI_ARVALID & my_source.S_AXI_ARREADY) implies (!my_source.S_AXI_RVALID) [*1:$] ##1 (my_source.S_AXI_RVALID && S_AXI_RREADY && my_source.S_AXI_RLAST));


// Write Transaction, Strict Ordering AXI4
P_19 : assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (S_AXI_AWVALID & my_source.S_AXI_AWREADY) implies (!my_source.S_AXI_WREADY) [*1:$] ##1 (my_source.S_AXI_WREADY && S_AXI_WVALID && S_AXI_WLAST));

// Write Transaction, Strict Ordering AXI4
P_20 : assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (S_AXI_AWVALID & my_source.S_AXI_AWREADY) ##1 (S_AXI_WVALID & my_source.S_AXI_WREADY & S_AXI_WLAST) implies (!my_source.S_AXI_BVALID) [*1:$] ##1 (my_source.S_AXI_BVALID && S_AXI_BREADY));


endmodule


bind my_source assert_axi4full sva_bind (.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),.S_AXI_AWADDR(S_AXI_AWADDR),.S_AXI_AWPROT(S_AXI_AWPROT),
.S_AXI_AWVALID(S_AXI_AWVALID),.S_AXI_WDATA(S_AXI_WDATA),.S_AXI_WSTRB(S_AXI_WSTRB),.S_AXI_WLAST(S_AXI_WLAST),.S_AXI_WVALID(S_AXI_WVALID),.S_AXI_BREADY(S_AXI_BREADY),.S_AXI_ARADDR(S_AXI_ARADDR),.S_AXI_ARPROT(S_AXI_ARPROT),.S_AXI_ARVALID(S_AXI_ARVALID),.S_AXI_RREADY(S_AXI_RREADY));
