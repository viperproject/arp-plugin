# ARP Plugin for Silver

Plugin to add Abstract Read Permissions support to Silver.

Adds support for read permission `rd`, counting permission `rdc(n)` for integer `n`,
wildcard permission `rdw` and token permission `rd_token(tk)` and `rd_token_fresh(tk)`
for some reference `tk`.

Read permission used in predicates is denoted as `rd_global`. In predicates the normal
`rd` qualifier can be used.

To use the plugin it has to be on the Java classpath. When invoking the back end
`--plugin viper.silver.plugin.ARPPlugin` has to be specified.
