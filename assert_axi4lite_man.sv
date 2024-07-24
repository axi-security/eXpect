module assert_axi4lite (
  // Global Clock Signal
  input wire  M_AXI_ACLK,
  // Global Reset Signal. This Signal is Active LOW
  input wire  M_AXI_ARESETN,

 input wire  M_AXI_AWREADY,
  // Write ready. This signal indicates that the slave
  // can accept the write data.
  input wire  M_AXI_WREADY,
  // Write response. This signal indicates the status
  // of the write transaction.
  input wire [1 : 0] M_AXI_BRESP,
  // Write response valid. This signal indicates that the channel
  // is signaling a valid write response.
  input wire  M_AXI_BVALID,
  // Read address ready. This signal indicates that the slave is
  // ready to accept an address and associated control signals.
  input wire  M_AXI_ARREADY,
  // Read data (issued by slave)
  input wire [31 : 0] M_AXI_RDATA,
// Read response. This signal indicates the status of the
  // read transfer.
  input wire [1 : 0] M_AXI_RRESP,
  // Read valid. This signal indicates that the channel is
  // signaling the required read data.
  input wire  M_AXI_RVALID
  );

  // Read Transaction, Channel Ordering
P_1 : assert property (@(posedge M_AXI_ACLK) (M_AXI_ARESETN && my_source.M_AXI_ARVALID && M_AXI_ARREADY) |-> (!(M_AXI_RVALID)));

// Write Transaction, Channel Ordering
P_2 : assert property (@(posedge M_AXI_ACLK) (M_AXI_ARESETN && my_source.M_AXI_WVALID && M_AXI_WREADY) |-> (!(M_AXI_BVALID)));

// Read Transaction, Stability, AR Channel
P_3_AR : assert property (@(posedge M_AXI_ACLK) disable iff ((my_source.M_AXI_ARVALID) && (M_AXI_ARREADY)) ((M_AXI_ARESETN) && (my_source.M_AXI_ARVALID) && (!M_AXI_ARREADY)) |=> (my_source.M_AXI_ARVALID));

// Read Transaction, Stability, R Channel
P_3_R: assert property (@(posedge M_AXI_ACLK) disable iff ((M_AXI_RVALID  ) && (my_source.M_AXI_RREADY )) ((M_AXI_ARESETN) && M_AXI_RVALID && (!my_source.M_AXI_RREADY)) |=> (M_AXI_RVALID ));

// Write Transaction, Stability, AW Channel
P_3_AW : assert property (@(posedge M_AXI_ACLK) ((M_AXI_ARESETN  ) && my_source.M_AXI_AWVALID && (!M_AXI_AWREADY)) |=> (my_source.M_AXI_AWVALID ));

// Write Transaction, Stability, W Channel
P_3_W: assert property (@(posedge M_AXI_ACLK) disable iff ((my_source.M_AXI_WVALID  ) && (M_AXI_WREADY )) ((M_AXI_ARESETN ) && my_source.M_AXI_WVALID && (!M_AXI_WREADY)) |=> (my_source.M_AXI_WVALID ));

// Write Transaction, Stability, B Channel
P_3_B: assert property (@(posedge M_AXI_ACLK) disable iff ((M_AXI_BVALID  ) && (my_source.M_AXI_BREADY )) ((M_AXI_ARESETN ) && M_AXI_BVALID && (!my_source.M_AXI_BREADY)) |=> (M_AXI_BVALID ));

// Read Transaction, Stability, ARADDR
P_4_AR: assert property (@(posedge M_AXI_ACLK) disable iff ((my_source.M_AXI_ARVALID  ) && (M_AXI_ARREADY )) ((M_AXI_ARESETN  ) && (my_source.M_AXI_ARVALID) && (!M_AXI_ARREADY)) |=> ($past(my_source.M_AXI_ARADDR) == my_source.M_AXI_ARADDR));

// Write Transaction, Stability, AWADDR
P_4_AW : assert property (@(posedge M_AXI_ACLK) disable iff ((my_source.M_AXI_AWVALID  ) && (M_AXI_AWREADY )) ((M_AXI_ARESETN ) && my_source.M_AXI_AWVALID && (!M_AXI_AWREADY)) |=>  $stable(my_source.M_AXI_AWADDR));

// Read Transaction, Stability, ARPROT
P_5_AR: assert property (@(posedge M_AXI_ACLK) disable iff ((my_source.M_AXI_ARVALID  ) && (M_AXI_ARREADY )) ((M_AXI_ARESETN ) && $rose(my_source.M_AXI_ARVALID) && (!M_AXI_ARREADY)) |=> ($past(my_source.M_AXI_ARPROT) == my_source.M_AXI_ARPROT));

// Read Transaction, Stability, AWPROT
P_5_AW : assert property (@(posedge M_AXI_ACLK) disable iff ((my_source.M_AXI_AWVALID  ) && (M_AXI_AWREADY )) ((M_AXI_ARESETN ) && my_source.M_AXI_AWVALID && (!M_AXI_AWREADY)) |=> $stable(my_source.M_AXI_AWPROT));

// Reset Mechanism, Handshake signals
P_6_1 : assert property (@(posedge M_AXI_ACLK) ($rose(M_AXI_ARESETN)) |-> (!my_source.M_AXI_ARVALID && !my_source.M_AXI_AWVALID && !my_source.M_AXI_WVALID));
// Reset Mechanism, Handshake signals
P_6_2 : assert property (@(posedge M_AXI_ACLK) ($fell(M_AXI_ARESETN)) |-> ##1 (!my_source.M_AXI_ARVALID && !my_source.M_AXI_AWVALID && !my_source.M_AXI_WVALID));


// Reset Mechanism, Subordinate driven, Handshake signals
P_7_1 : assert property (@(posedge M_AXI_ACLK) ($rose(M_AXI_ARESETN)) |-> (!M_AXI_RVALID && !M_AXI_BVALID));
// Reset Mechanism, Subordinate driven, Handshake signals
P_7_2 : assert property (@(posedge M_AXI_ACLK) ($fell(M_AXI_ARESETN)) |-> ##1 (!M_AXI_RVALID && !M_AXI_BVALID));

// Read Transaction, Sensitive Data Stability, RDATA
P_8_R : assert property (@(posedge M_AXI_ACLK) disable iff ((M_AXI_RVALID  ) && (my_source.M_AXI_RREADY )) ((M_AXI_ARESETN ) && M_AXI_RVALID && (!my_source.M_AXI_RREADY)) |=> ($stable(M_AXI_RDATA)));

// Write Transaction, Sensitive Data Stability, WDATA
P_8_W : assert property (@(posedge M_AXI_ACLK) disable iff ((my_source.M_AXI_WVALID  ) && (M_AXI_WREADY )) ((M_AXI_ARESETN ) && my_source.M_AXI_WVALID && (!M_AXI_WREADY)) |=> $stable(my_source.M_AXI_WDATA));

// Read Transaction, Sensitive Data Stability, RRESP
P_9_R : assert property (@(posedge M_AXI_ACLK) disable iff ((M_AXI_RVALID  ) && (my_source.M_AXI_RREADY )) ((M_AXI_ARESETN ) && M_AXI_RVALID && (!my_source.M_AXI_RREADY)) |=> $stable(M_AXI_RRESP));

// Write Transaction, Sensitive Data Stability, BRESP
P_9_B: assert property (@(posedge M_AXI_ACLK) disable iff ((M_AXI_BVALID  ) && (my_source.M_AXI_BREADY )) ((M_AXI_ARESETN ) && M_AXI_BVALID && (!my_source.M_AXI_BREADY)) |=> $stable(M_AXI_BRESP));

// AXI4-Lite, Error Handling
P_10_B : assert property (@(posedge M_AXI_ACLK) (M_AXI_ARESETN & M_AXI_BVALID) |-> ((M_AXI_BRESP == 2'b00) ||  (M_AXI_BRESP == 2'b10) ||(M_AXI_BRESP == 2'b11)));

// AXI4-Lite, Error Handling
P_10_R : assert property (@(posedge M_AXI_ACLK) (M_AXI_ARESETN & M_AXI_RVALID) |-> ((M_AXI_RRESP == 2'b00) || (M_AXI_BRESP == 2'b10) || (M_AXI_RRESP == 2'b11)));

// Read Transaction, Strict Ordering
P_11 : assert property (@(posedge M_AXI_ACLK) disable iff (!M_AXI_ARESETN) (my_source.M_AXI_ARVALID & M_AXI_ARREADY) implies (!M_AXI_RVALID) [*1:$] ##1 (M_AXI_RVALID && my_source.M_AXI_RREADY));

// Write Transaction, Strict Ordering
P_12 : assert property (@(posedge M_AXI_ACLK) disable iff (!M_AXI_ARESETN) (my_source.M_AXI_AWVALID & M_AXI_AWREADY) implies (!M_AXI_WREADY) [*1:$] ##1 (M_AXI_WREADY && my_source.M_AXI_WVALID));

// Write Transaction, Strict Ordering
P_13 : assert property (@(posedge M_AXI_ACLK) disable iff (!M_AXI_ARESETN) (my_source.M_AXI_AWVALID & M_AXI_AWREADY) ##1 (my_source.M_AXI_WVALID & M_AXI_WREADY) implies (!M_AXI_BVALID) [*1:$] ##1 (M_AXI_BVALID && my_source.M_AXI_BREADY));

// Reset Mechanism, Subordinate driven, RDATA and RESP
P_14_1 : assert property (@(posedge M_AXI_ACLK) ($rose(M_AXI_ARESETN)) |-> ((M_AXI_RDATA == 0) && (M_AXI_RRESP == 2'b00) && (M_AXI_BRESP == 2'b00)));
  
// Reset Mechanism, Subordinate driven, RDATA and RESP
P_14_2 : assert property (@(posedge M_AXI_ACLK) ($fell(M_AXI_ARESETN)) |-> ##1 ((M_AXI_RDATA == 0) && (M_AXI_RRESP == 2'b00) && (M_AXI_BRESP == 2'b00)));
  
// Reset Mechanism, Manager drive, ADDR, WDATA, PROT
P_15_1 : assert property (@(posedge M_AXI_ACLK) ($rose(M_AXI_ARESETN)) |-> ((my_source.M_AXI_ARADDR == 0) && (my_source.M_AXI_AWADDR == 0) && (my_source.M_AXI_WDATA == 0) && (my_source.M_AXI_ARPROT == 3'b000) && (my_source.M_AXI_AWPROT == 3'b000)));

// Reset Mechanism, Manager driven, ADDR, WDATA, PROT
P_15_2 : assert property (@(posedge M_AXI_ACLK) ($fell(M_AXI_ARESETN)) |-> ##1 ((my_source.M_AXI_ARADDR == 0) && (my_source.M_AXI_AWADDR == 0) && (my_source.M_AXI_WDATA == 0) && (my_source.M_AXI_ARPROT == 3'b000) && (my_source.M_AXI_AWPROT == 3'b000)));

// Read Transaction, Subordinate driven, Data Invalidation
P_16 : assert property (@(posedge M_AXI_ACLK) disable iff (!M_AXI_ARESETN) (!M_AXI_RVALID) |-> M_AXI_RDATA == 0);


endmodule


bind my_source assert_axi4lite sva_bind (.M_AXI_ACLK(M_AXI_ACLK), .M_AXI_ARESETN(M_AXI_ARESETN),.M_AXI_AWREADY(M_AXI_AWREADY),.M_AXI_WREADY(M_AXI_WREADY),.M_AXI_BRESP(M_AXI_BRESP),.M_AXI_BVALID(M_AXI_BVALID),.M_AXI_ARREADY(M_AXI_ARREADY),.M_AXI_RDATA(M_AXI_RDATA),.M_AXI_RRESP(M_AXI_RRESP),.M_AXI_RVALID(M_AXI_RVALID));
