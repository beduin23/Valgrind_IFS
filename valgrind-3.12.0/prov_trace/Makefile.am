include $(top_srcdir)/Makefile.tool.am

EXTRA_DIST = docs/pt-manual.xml

#----------------------------------------------------------------------------
# prov_trace-<platform>
#----------------------------------------------------------------------------

noinst_PROGRAMS  = prov_trace-@VGCONF_ARCH_PRI@-@VGCONF_OS@
if VGCONF_HAVE_PLATFORM_SEC
noinst_PROGRAMS += prov_trace-@VGCONF_ARCH_SEC@-@VGCONF_OS@
endif

PROV_TRACE_SOURCES_COMMON = pt_main.c

prov_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_SOURCES      = \
	$(PROV_TRACE_SOURCES_COMMON)
prov_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
prov_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS       = \
	$(AM_CFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
prov_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_PRI_CAPS@)
prov_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_PRI_CAPS@)
prov_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
prov_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_PRI@ \
	$(LINK) \
	$(prov_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS) \
	$(prov_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS)

if VGCONF_HAVE_PLATFORM_SEC
prov_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_SOURCES      = \
	$(PROV_TRACE_SOURCES_COMMON)
prov_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
prov_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS       = \
	$(AM_CFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
prov_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_SEC_CAPS@)
prov_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_SEC_CAPS@)
prov_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
prov_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_SEC@ \
	$(LINK) \
	$(prov_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS) \
	$(prov_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS)
endif


