import http.server
import os
os.chdir(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "assets"))
http.server.test(HandlerClass=http.server.SimpleHTTPRequestHandler, port=8090)
