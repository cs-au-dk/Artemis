Ajax Server Interface Description Language (AIL)
================================================

Artemis supports the usage of AIL descriptions when testing web applications. An AIL description is a specification of the client-server communication conducted using Ajax. These descriptions allow Artemis to test the client-side without a concrete instance of the server-side.

This functionality is described in more detail in *Server Interface Descriptions for Automated Testing of JavaScript Web Applications, Casper S. Jensen, Anders Møller and Zhendong Su. ESEC/FSE 2013.*

Using AIL Descriptions
----------------------

AIL descriptions is used by Artemis through the ``ailproxy.js`` HTTP proxy. This proxy accepts an AIL description file and acts as a mock server listening on localhost port 8080. 

To use this proxy Artemis must be run using the ``-t`` argument.

Generating AIL Descriptions
---------------------------

AIL descriptions can be tedious to write by hand. This can be mitigated by using the AIL learning algorithm provided in the ``contrib`` folder. The AIL learning algorithm uses a dump (raw) of concrete client-server traffic to generate an AIL description.

The *raw* traffic can be collected by using the `HTTPdump proxy <https://github.com/sema/HTTPdump>`_.

The learning algorithm is provided as a python script in the ``contrib/ajaxinterface`` folder.
