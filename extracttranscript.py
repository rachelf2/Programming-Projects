#!/bin/python
#takes in HTML webpage containing a transcript of audio from a sports broadcast. 
#Extracts the transcript, tokenizes it and tags it for part of speech.
from HTMLParser import HTMLParser
import sys
import nltk
from nltk.stem.lancaster import LancasterStemmer
st= LancasterStemmer()

class FindTranscript(HTMLParser):
  def __init__(self):
    HTMLParser.__init__(self)
    self.encode= False
    self.data = ""

  def handle_starttag(self, tag, attributes):
    if tag != 'div':
      return
    for name, value in attributes:
      if name == 'id' and value == 'ez-transcript-text':
        self.encode= True
        break
      else:
        return

  def handle_endtag(self, tag):
    if tag == 'div' and self.encode:
      transcript=prepareTrans(self.data)
      trans_file = open(sys.argv[1].split(".")[0] + ".transcript",'w')
      trans_file.write(transcript)
      trans_file.close()
      self.encode=False

  def handle_data(self, data):
    if self.encode:
      self.data += data

def prepareTrans(trans):
  transcript = nltk.word_tokenize(trans)
  transcript = nltk.tag.pos_tag(transcript)
  trans_pos = ''
  for tagged_token in transcript:
    word= tagged_token[0]
    stem= st.stem(word)
    pos= tagged_token[1]
    string= str(word) + '\t' + str(pos) + '\t' + str(stem) + '\n'
    string= string.expandtabs(16)
    trans_pos = trans_pos + string
  return trans_pos

def run_extract():  
  parser = FindTranscript()
  fid= open (sys.argv[1], 'r')
  text= file.read(fid)
  parser.feed(text)
  fid.close()
