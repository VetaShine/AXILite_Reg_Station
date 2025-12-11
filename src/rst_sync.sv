module rst_sync #(
    parameter bit RST_SYNC_EN = 1'b0,
    parameter int DEPTH       = 2
) (
    input   clk      ,
    input   aresetn  ,
    output  reset_out
);
    if (RST_SYNC_EN) begin: gen_enabled
        logic [DEPTH - 1 : 0] chain;

        always_ff @(posedge clk or negedge aresetn) begin
            if (!aresetn) begin
                chain <= '0;
            end else begin
                chain <= {chain[DEPTH - 2 : 0], 1'b1};
            end
        end

        assign reset_out = chain[DEPTH - 1]; 
    end else begin: gen_disabled
        assign reset_out = aresetn;
    end
endmodule
